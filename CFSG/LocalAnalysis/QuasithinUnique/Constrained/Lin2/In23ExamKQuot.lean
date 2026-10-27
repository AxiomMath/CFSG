module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBasic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Central

variable {X : Type} [Group X]

theorem not_isSolvable_map_center {H : Subgroup X} (hH : ¬ Group.IsSolvable ↥H) :
    ¬ Group.IsSolvable ↥(H.map (QuotientGroup.mk' (Subgroup.center X))) := by
  intro hsolv
  apply hH
  let g : ↥H →* ↥(H.map (QuotientGroup.mk' (Subgroup.center X))) :=
    ((QuotientGroup.mk' (Subgroup.center X)).comp H.subtype).codRestrict _
      (fun x => Subgroup.mem_map_of_mem _ x.2)
  have hg : Function.Surjective g := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Group.IsSolvable ↥g.ker := by
    have : IsMulCommutative ↥g.ker := ⟨⟨fun a b => by
      have ha : ((a : ↥H) : X) ∈ Subgroup.center X := by
        have := a.2
        rw [MonoidHom.mem_ker] at this
        have h2 := congrArg Subtype.val this
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hb : ((b : ↥H) : X) ∈ Subgroup.center X := by
        have := b.2
        rw [MonoidHom.mem_ker] at this
        have h2 := congrArg Subtype.val this
        exact (QuotientGroup.eq_one_iff _).mp h2
      apply Subtype.ext
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp ha _).symm⟩⟩
    infer_instance
  exact Group.isSolvable_of_ker_le_range (g.ker.subtype) g (by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

variable [Finite X]

theorem card_le_pCore_of_central' {Y : Subgroup X} (hY : Y ≤ Subgroup.center X)
    (hp : IsPGroup 2 Y) : Nat.card Y ≤ Nat.card (CFSG.Open.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : Y.Normal := ⟨fun n hn g => by
    have h1 := Subgroup.mem_center_iff.mp (hY hn) g
    have h2 : g * n * g⁻¹ = n := by rw [h1, mul_inv_cancel_right]
    rw [h2]
    exact hn⟩
  exact Subgroup.card_le_of_le (CFSG.LieType.BorelTits.le_pCore 2 hnorm hp)

end Central

section Config

variable {G : Type} [Group G] [Finite G] {K B B' P R : Subgroup G} {m : ℕ}

omit [Finite G] in
theorem ExamConfig.blockU_le_B (h : ExamConfig K B B' P R m) : blockU B ≤ B :=
  (C1.blockU_le_blockQ h.short).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 B)

omit [Finite G] in
theorem ExamConfig.not_isSolvable_B (h : ExamConfig K B B' P R m) : ¬ Group.IsSolvable ↥B := by
  obtain ⟨F, _, _, hF, α, hα, -⟩ := h.lin2
  intro hB
  have hm := h.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFc : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card]; exact hF
  have hcp : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hFc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have hsimple := Vol2Native.A312L.sl2_isSimple hK4
  have hnab := Vol2Native.A312L.sl2_nonabelian hK4
  have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective hα
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem ExamConfig.exists_bar (h : ExamConfig K B B' P R m) :
    ∃ Abar Bbar : Subgroup (↥K ⧸ Subgroup.center ↥K),
      Abar ≠ ⊥ ∧ IsPGroup 2 Abar ∧
      Bbar ≤ Subgroup.normalizer (Abar : Set (↥K ⧸ Subgroup.center ↥K)) ∧
      ¬ Group.IsSolvable ↥Bbar := by
  have hBK : B ≤ K := h.le_K
  have hAB : blockU B ≤ B := h.blockU_le_B
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set AK : Subgroup ↥K := (blockU B).subgroupOf K with hAK
  set BK : Subgroup ↥K := B.subgroupOf K with hBKdef
  have hAKcard : Nat.card AK = 2 ^ (3 * m) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAB.trans hBK)).toEquiv, h.card_U]
  have hAKp : IsPGroup 2 AK := IsPGroup.of_card hAKcard
  refine ⟨AK.map π, BK.map π, ?_, hAKp.map π, ?_, ?_⟩
  · intro hbot
    have hle : AK ≤ Subgroup.center ↥K := by
      intro a ha
      have : π a ∈ AK.map π := Subgroup.mem_map_of_mem _ ha
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have h1 := card_le_pCore_of_central' hle hAKp
    rw [hAKcard] at h1
    have h2 := h.card_pCore_group
    have hm := h.two_le
    have h3 : 2 ^ 4 ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  ·
    have key : ∀ x ∈ BK.map π, ∀ y ∈ AK.map π, x * y * x⁻¹ ∈ AK.map π := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
      refine ⟨b * a * b⁻¹, ?_, by simp [map_mul]⟩
      have hb' : (b : G) ∈ B := hb
      have ha' : (a : G) ∈ blockU B := ha
      have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hb') (a : G)).mp ha'
      exact this
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key x hx y, fun hy => ?_⟩
    have hxinv : x⁻¹ ∈ BK.map π := inv_mem hx
    have := key x⁻¹ hxinv _ hy
    simpa [mul_assoc] using this
  · exact not_isSolvable_map_center (fun hs => h.not_isSolvable_B
      (Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBK).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hBK).surjective))

end Config

end CFSG.QuasithinUnique.Lin2
