module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof

open scoped commutatorElement

section Center

variable {L : Type*} [Group L]

theorem isPerfect_of_isQuasisimple (hq : CFSG.Open.IsQuasisimple L) : Group.IsPerfect L :=
  Group.isPerfect_def.mpr hq.1

theorem pow_three_eq_one_of_mem_center (hZ : Nat.card (Subgroup.center L) = 3) {z : L}
    (hz : z ∈ Subgroup.center L) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨z, hz⟩)
  rw [hZ] at h
  simpa using congrArg Subtype.val h

theorem exists_mem_center_ne_one (hZ : Nat.card (Subgroup.center L) = 3) :
    ∃ z ∈ Subgroup.center L, z ≠ 1 := by
  by_contra h
  have hbot : Subgroup.center L = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun z hz => by_contra fun hne => h ⟨z, hz, hne⟩
  rw [hbot, Subgroup.card_bot] at hZ
  omega

theorem mem_center_cases (hZ : Nat.card (Subgroup.center L) = 3) {z : L}
    (hz : z ∈ Subgroup.center L) (hz1 : z ≠ 1) {w : L} (hw : w ∈ Subgroup.center L) :
    w = 1 ∨ w = z ∨ w = z ^ 2 := by
  classical
  haveI : Finite (Subgroup.center L) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : (⟨z, hz⟩ : Subgroup.center L) ^ 3 = 1 :=
    Subtype.ext (pow_three_eq_one_of_mem_center hZ hz)
  have hz1' : (⟨z, hz⟩ : Subgroup.center L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hord : orderOf (⟨z, hz⟩ : Subgroup.center L) = 3 := orderOf_eq_prime hz3 hz1'
  have htop : Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center L) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hZ]
  have hw' : (⟨w, hw⟩ : Subgroup.center L) ∈ Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center L) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hw'
  simp only [Finset.mem_image, Finset.mem_range] at hw'
  obtain ⟨a, ha, haw⟩ := hw'
  have hwa : z ^ a = w := congrArg Subtype.val haw
  interval_cases a
  · exact Or.inl (by simpa using hwa.symm)
  · exact Or.inr (Or.inl (by simpa using hwa.symm))
  · exact Or.inr (Or.inr hwa.symm)

theorem eq_top_of_sup_center_eq_top_aux1 (n n' z z' : L) (hz : z ∈ Subgroup.center L)
    (hz' : z' ∈ Subgroup.center L) : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
  have hc : ∀ a c : L, c ∈ Subgroup.center L → ⁅c, a⁆ = 1 := fun a c hc =>
    Commute.commutator_eq (Subgroup.mem_center_iff.mp hc a).symm
  have hc' : ∀ a c : L, c ∈ Subgroup.center L → ⁅a, c⁆ = 1 := fun a c hc =>
    Commute.commutator_eq (Subgroup.mem_center_iff.mp hc a)
  rw [commutatorElement_mul_left_eq_conj_mul, hc _ _ hz, commutatorElement_mul_right_eq_mul_conj,
    hc' _ _ hz']
  simp

theorem eq_top_of_sup_center_eq_top (hq : CFSG.Open.IsQuasisimple L) {N : Subgroup L}
    (h : N ⊔ Subgroup.center L = ⊤) : N = ⊤ := by
  have hle : commutator L ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ g' _
    have hg : g ∈ N ⊔ Subgroup.center L := h ▸ Subgroup.mem_top g
    have hg' : g' ∈ N ⊔ Subgroup.center L := h ▸ Subgroup.mem_top g'
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg'
    rw [eq_top_of_sup_center_eq_top_aux1 n n' z z' hz hz', commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
  rw [hq.1] at hle
  exact top_le_iff.mp hle

theorem injective_of_center_ne_one {M : Type*} [Group M] (hq : CFSG.Open.IsQuasisimple L)
    (hZ : Nat.card (Subgroup.center L) = 3) (f : L →* M)
    (hz : ∃ z ∈ Subgroup.center L, f z ≠ 1) : Function.Injective f := by
  obtain ⟨z, hz, hfz⟩ := hz
  have hKZ : f.ker ⊓ Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwK, hwZ⟩
    rw [Subgroup.mem_bot]
    by_contra hw1
    rcases mem_center_cases hZ hwZ hw1 hz with h | h | h
    · exact hfz (by rw [h, map_one])
    · exact hfz (by rw [h]; exact hwK)
    · exact hfz (by rw [h, map_pow, MonoidHom.mem_ker.mp hwK, one_pow])
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hker
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  haveI hnorm : (f.ker.map (QuotientGroup.mk' (Subgroup.center L))).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top (f.ker.map (QuotientGroup.mk' (Subgroup.center L)))
    with h | h
  · have hle : f.ker ≤ Subgroup.center L := by
      intro x hx
      have hx' : QuotientGroup.mk' (Subgroup.center L) x ∈
          f.ker.map (QuotientGroup.mk' (Subgroup.center L)) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).mp hx'
    apply hker
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ f.ker ⊓ Subgroup.center L := ⟨hx, hle hx⟩
    rwa [hKZ] at hx'
  · have hsup : f.ker ⊔ Subgroup.center L = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center L)) f.ker
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hK : f.ker = ⊤ := eq_top_of_sup_center_eq_top hq hsup
    apply hfz
    have hzK : z ∈ f.ker := hK ▸ Subgroup.mem_top z
    exact MonoidHom.mem_ker.mp hzK

theorem card_eq_1080 [Finite L] (hZ : Nat.card (Subgroup.center L) = 3)
    (e6 : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)) : Nat.card L = 1080 := by
  have h1 : Nat.card (L ⧸ Subgroup.center L) = 360 := by
    rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L), h1, hZ]

theorem dvd_27_card [Finite L] (hZ : Nat.card (Subgroup.center L) = 3)
    (e6 : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)) : 27 ∣ Nat.card L := by
  rw [card_eq_1080 hZ e6]
  norm_num

end Center

theorem exists_center_of_conj {G : Type*} [Group G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) :
    ∃ w : ↥L, w ∈ Subgroup.center ↥L ∧ (w : G) = b * (z : G) * b⁻¹ := by
  have hconj : ∀ h : G, h ∈ L ↔ b * h * b⁻¹ ∈ L := Subgroup.mem_set_normalizer_iff.mp hb
  have hconj' : ∀ h : G, h ∈ L ↔ b⁻¹ * h * b ∈ L := Subgroup.mem_set_normalizer_iff''.mp hb
  refine ⟨⟨b * (z : G) * b⁻¹, (hconj _).mp z.2⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg' : b⁻¹ * (g : G) * b ∈ L := (hconj' _).mp g.2
  have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b⁻¹ * (g : G) * b, hg'⟩)
  simp only [Subgroup.coe_mul] at hcomm
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  calc (g : G) * (b * (z : G) * b⁻¹) = b * (b⁻¹ * (g : G) * b * (z : G)) * b⁻¹ := by group
    _ = b * ((z : G) * (b⁻¹ * (g : G) * b)) * b⁻¹ := by rw [hcomm]
    _ = b * (z : G) * b⁻¹ * (g : G) := by group

end CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof
