module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620FStar
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

private theorem Data620.fsm_core_le (_h : Data620 M B H S K z b f) : pCoreOf 2 H ≤ H :=
  CFSG.openPCoreOf_le 2 H

private theorem Data620.fsm_isPGroup_core (h : Data620 M B H S K z b f) :
    IsPGroup 2 (pCoreOf 2 H) :=
  h.maxInv.1.2.1.to_le h.core_le

private theorem Data620.fsm_core_conj (h : Data620 M B H S K z b f) {n : G} (hn : n ∈ H)
    {x : G} (hx : x ∈ pCoreOf 2 H) : n * x * n⁻¹ ∈ pCoreOf 2 H :=
  (mem_normalizer_iff.1 (h.eq_normalizer.le hn) x).1 hx

private theorem Data620.fsm_normal (h : Data620 M B H S K z b f) :
    ((pCoreOf 2 H).subgroupOf H).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.fsm_core_le).2 h.eq_normalizer.le

private theorem Data620.fsm_exists_mul (h : Data620 M B H S K z b f) {a : G} (haS : a ∈ S)
    (ha : a ∈ K ⊔ pCoreOf 2 H) : ∃ k ∈ K ⊓ S, ∃ o ∈ pCoreOf 2 H, a = k * o := by
  rw [← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H) (h.K_le.trans h.eq_normalizer.le)] at ha
  obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 ha
  refine ⟨k, ⟨hk, ?_⟩, o, ho, rfl⟩
  simpa using S.mul_mem haS (S.inv_mem (h.core_le ho))

omit [Finite G] in
private theorem fsm_le_normalizer_map {H : Subgroup G} (L : Subgroup ↥H) [L.Normal] :
    H ≤ normalizer ((L.map H.subtype : Subgroup G) : Set G) := by
  have hsub : (L.map H.subtype).subgroupOf H = L :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le L)).1 (by rw [hsub]; infer_instance)

omit [Finite G] in
private theorem fsm_mk_comm_iff {H O : Subgroup G} {N : Subgroup ↥H} [N.Normal]
    (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ O) (y k : ↥H) :
    QuotientGroup.mk' N y * QuotientGroup.mk' N k =
      QuotientGroup.mk' N k * QuotientGroup.mk' N y ↔
    (y : G) * k * (y : G)⁻¹ * (k : G)⁻¹ ∈ O := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
    QuotientGroup.ker_mk', hN]
  rfl

private theorem Data620.fsm_normal_Kb (h : Data620 M B H S K z b f) {N : Subgroup ↥H}
    [N.Normal] : ((K.subgroupOf H).map (QuotientGroup.mk' N)).Normal := by
  have : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer h.K_le).2 h.K_normal
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

private theorem Data620.fsm_exists_equiv (h : Data620 M B H S K z b f) {N : Subgroup ↥H}
    [N.Normal] (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) :
    Nonempty (↥((K.subgroupOf H).map (QuotientGroup.mk' N)) ≃* GL32) := by
  let ψ : ↥K →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion h.K_le)
  have hrange : ψ.range = (K.subgroupOf H).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ψ.ker = f.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, h.f_ker]
    exact (QuotientGroup.eq_one_iff (N := N) _).trans (hN _)
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f h.f_surj)))⟩

private theorem fsm_isSimpleGroup_GL32 : IsSimpleGroup GL32 := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  exact L32Insp.pslEquiv.symm.isSimpleGroup

private theorem fsm_GL32_noncomm : ∃ a c : GL32, a * c ≠ c * a := by
  refine ⟨L32Insp.tL, L32Insp.l₀, fun hcomm => ?_⟩
  have h1 : L32Insp.tL * L32Insp.l₀ * L32Insp.tL⁻¹ = L32Insp.l₀ := by
    rw [hcomm]
    group
  rw [L32Insp.tL_conj_l₀, inv_eq_iff_eq_inv] at h1
  have h2 : L32Insp.l₀ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel _
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [L32Insp.orderOf_l₀] at h3
  omega

private theorem fsm_Kb_facts {Y : Type*} [Group Y] {Kb : Subgroup Y} (e : ↥Kb ≃* GL32) :
    IsSimpleGroup ↥Kb ∧ (∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a) ∧ 3 ∣ Nat.card Kb := by
  have := fsm_isSimpleGroup_GL32
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a, c, hac⟩ := fsm_GL32_noncomm
    refine ⟨(e.symm a : Y), (e.symm a).2, (e.symm c : Y), (e.symm c).2, fun hcomm => hac ?_⟩
    have h1 : e.symm a * e.symm c = e.symm c * e.symm a := Subtype.ext hcomm
    refine e.symm.injective ?_
    rw [map_mul, map_mul]
    exact h1
  · rw [Nat.card_congr e.toEquiv, L32Insp.card_GL]
    norm_num

private theorem Data620.fsm_orderOf_b (h : Data620 M B H S K z b f) {N : Subgroup ↥H}
    [N.Normal] (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) :
    orderOf (QuotientGroup.mk' N (⟨b, h.B_le h.b_mem⟩ : ↥H)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := fun e => by
    have := h.b_order
    rw [e, orderOf_one] at this
    omega
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨b, h.B_le h.b_mem⟩ : ↥H) ^ 3 = 1 :=
      Subtype.ext (by simpa [h.b_order] using pow_orderOf_eq_one b)
    rw [this, map_one]
  · intro e
    have hbO := (hN _).1 ((QuotientGroup.eq_one_iff (N := N) (⟨b, h.B_le h.b_mem⟩ : ↥H)).1 e)
    exact hb1 (h.b_fpf b hbO rfl)

private theorem Data620.fsm_cent_b (h : Data620 M B H S K z b f) {N : Subgroup ↥H}
    [N.Normal] (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) :
    QuotientGroup.mk' N (⟨b, h.B_le h.b_mem⟩ : ↥H) ∈
      centralizer (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup _) : Set _) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  refine ((fsm_mk_comm_iff hN _ _).2 ?_).symm
  exact h.b_cent (commutator_mem_commutator (mem_zpowers b) hk)

private theorem Data620.fsm_sup_eq (h : Data620 M B H S K z b f) {N : Subgroup ↥H} [N.Normal] :
    (K.subgroupOf H).map (QuotientGroup.mk' N) ⊔
        zpowers (QuotientGroup.mk' N (⟨b, h.B_le h.b_mem⟩ : ↥H)) =
      ((K ⊔ B).subgroupOf H).map (QuotientGroup.mk' N) := by
  have hb : b ∈ H := h.B_le h.b_mem
  have hKB : K ⊔ B = K ⊔ zpowers b := by
    rw [h.B_eq, ← sup_assoc, sup_eq_left.2 (zpowers_le.2 h.z_mem_K)]
  have hz : (zpowers b).subgroupOf H = zpowers (⟨b, hb⟩ : ↥H) := by
    have h1 : (zpowers (⟨b, hb⟩ : ↥H)).map H.subtype = zpowers b := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← h1]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [hKB, subgroupOf_sup h.K_le (zpowers_le.2 hb), hz, Subgroup.map_sup,
    MonoidHom.map_zpowers]

private theorem Data620.fsm_primeCore (h : Data620 M B H S K z b f) {N : Subgroup ↥H}
    [N.Normal] (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) (N₁ : Subgroup (↥H ⧸ N))
    (hN₁ : N₁.Normal) (hcop : Nat.Coprime 3 (Nat.card N₁)) : N₁ = ⊥ := by
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have : (N₁.comap (QuotientGroup.mk' N)).Normal := hN₁.comap _
  have hN2 : IsPGroup 2 ↥N := by
    intro g
    obtain ⟨k, hk⟩ := h.fsm_isPGroup_core ⟨((g : ↥H) : G), (hN _).1 g.2⟩
    have := congrArg Subtype.val hk
    exact ⟨k, Subtype.ext (Subtype.ext this)⟩
  have hcardN : Nat.Coprime 3 (Nat.card N) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hcard : Nat.card (N₁.comap (QuotientGroup.mk' N)) = Nat.card N₁ * Nat.card N := by
    have h1 := relIndex_mul_card (QuotientGroup.mk' N).ker (N₁.comap (QuotientGroup.mk' N))
    rw [inf_of_le_left (MonoidHom.ker_le_comap _ N₁), relIndex_ker,
      map_comap_eq_self_of_surjective hsurj, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hle := h.primeCore_le ((N₁.comap (QuotientGroup.mk' N)).map H.subtype) (map_subtype_le _)
    (fsm_le_normalizer_map _) (by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
      exact Nat.Coprime.mul_right hcop hcardN)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨y, rfl⟩ := hsurj y
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff (N := N) y).2 ((hN y).2 (hle ⟨y, hy, rfl⟩))

private theorem Data620.fsm_three_le (h : Data620 M B H S K z b f) {N : Subgroup ↥H} [N.Normal]
    (P₁ : Subgroup (↥H ⧸ N)) (hP : IsPGroup 3 P₁) : Nat.card P₁ ≤ 9 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h1 : 3 ^ k ∣ Nat.card H :=
    hk ▸ (card_subgroup_dvd_card P₁).trans (card_quotient_dvd_card N)
  have h2 : Nat.card H = B.relIndex H * 9 := by
    have := relIndex_mul_card B H
    rw [inf_of_le_left h.B_le, h.B_card] at this
    exact this.symm
  have h3 : Nat.Coprime (3 ^ k) (B.relIndex H) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h.B_sylow)
  rw [h2] at h1
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) (h3.dvd_of_dvd_mul_left h1)

private theorem Data620.fsm_conj_mem (h : Data620 M B H S K z b f) {N : Subgroup ↥H} [N.Normal]
    (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) {y : ↥H}
    (hy : QuotientGroup.mk' N y ∈
      centralizer (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup _) : Set _))
    {s : G} (hs : s ∈ S) : (y : G) * s * (y : G)⁻¹ ∈ S := by
  obtain ⟨k, ⟨hkK, hkS⟩, o, ho, rfl⟩ := h.fsm_exists_mul hs (h.S_le hs)
  have hc : (y : G) * k * (y : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    (fsm_mk_comm_iff hN y ⟨k, h.K_le hkK⟩).1
      (mem_centralizer_iff.1 hy _ ⟨⟨k, h.K_le hkK⟩, hkK, rfl⟩).symm
  have e : (y : G) * (k * o) * (y : G)⁻¹ =
      ((y : G) * k * (y : G)⁻¹ * k⁻¹) * k * ((y : G) * o * (y : G)⁻¹) := by group
  rw [e]
  exact S.mul_mem (S.mul_mem (h.core_le hc) hkS) (h.core_le (h.fsm_core_conj y.2 ho))

private theorem Data620.fsm_cent_le (h : Data620 M B H S K z b f) {N : Subgroup ↥H} [N.Normal]
    (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) :
    ((centralizer (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup _) : Set _)).comap
      (QuotientGroup.mk' N)).map H.subtype ≤ M := by
  have hnorm : ((centralizer (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup _) :
      Set _)).comap (QuotientGroup.mk' N)).map H.subtype ≤ normalizer (S : Set G) := by
    rw [le_normalizer_iff]
    rintro _ ⟨y, hy, rfl⟩ s hs
    exact h.fsm_conj_mem hN hy hs
  have hlt : pCoreOf 2 H < S := by
    refine lt_of_le_of_ne h.core_le fun e => ?_
    have h4 := h.S_index
    rw [e, relIndex_self] at h4
    omega
  exact hnorm.trans (h.norm_le S hlt le_rfl (sup_le (le_normalizer) h.maxInv.1.2.2))

private theorem Data620.fsm_solvable (h : Data620 M B H S K z b f) {N : Subgroup ↥H} [N.Normal]
    (hN : ∀ g : ↥H, g ∈ N ↔ (g : G) ∈ pCoreOf 2 H) :
    Group.IsSolvable ↥(centralizer
      (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N))) := by
  have := h.M_solvable
  let C := centralizer
    (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N))
  let C₀ : Subgroup ↥H := C.comap (QuotientGroup.mk' N)
  have hC₀ : C₀.map H.subtype ≤ M := h.fsm_cent_le hN
  let j : ↥C₀ →* ↥M := (H.subtype.comp C₀.subtype).codRestrict M (fun x => hC₀ ⟨x, x.2, rfl⟩)
  have hj : Function.Injective j := fun x y hxy => by
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have : Group.IsSolvable ↥C₀ := Group.isSolvable_of_isSolvable_injective hj
  let ρ : ↥C₀ →* ↥C := ((QuotientGroup.mk' N).comp C₀.subtype).codRestrict C (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N c
    exact ⟨⟨y, hc⟩, rfl⟩
  exact Group.isSolvable_of_surjective hρ

theorem Data620.fStarEq (h : Data620 M B H S K z b f) :
    FStarQuotientEq H (pCoreOf 2 H) (K ⊔ B) := by
  have hNn := h.fsm_normal
  refine ⟨hNn, ?_⟩
  have hN : ∀ g : ↥H, g ∈ (pCoreOf 2 H).subgroupOf H ↔ (g : G) ∈ pCoreOf 2 H :=
    fun _ => Iff.rfl
  obtain ⟨e⟩ := h.fsm_exists_equiv hN
  obtain ⟨hsimple, hnc, h3dvd⟩ := fsm_Kb_facts e
  have hcard : Nat.card (zpowers (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H)
      (⟨b, h.B_le h.b_mem⟩ : ↥H))) = 3 := by
    rw [Nat.card_zpowers, h.fsm_orderOf_b hN]
  obtain ⟨-, hF⟩ := genFittingFStar_eq_sup_of_centralizer_solvable _ _ h.fsm_normal_Kb hsimple
    hnc h3dvd hcard (zpowers_le.2 (h.fsm_cent_b hN)) (h.fsm_primeCore hN)
    (fun P₁ hP => h.fsm_three_le P₁ hP) (h.fsm_solvable hN)
  exact hF.trans h.fsm_sup_eq

end CFSG.LocalAnalysis.RankThreeTheoremC
