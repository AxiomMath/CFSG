module

public import CFSG.LargeExtraspecial.AS35WLocal
public import CFSG.LargeExtraspecial.AS62Iso
public import CFSG.Quasithin.Background.TwoReduced

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Quasithin CFSG.Open AS62.Sem

namespace AS62

theorem isPGroup_pCoreOf (p : ℕ) {X : Type*} [Group X] (K : Subgroup X) :
    IsPGroup p (pCoreOf p K) := by
  rw [pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem conj_mem_pCoreOf (p : ℕ) {X : Type*} [Group X] {K : Subgroup X} {k o : X} (hk : k ∈ K)
    (ho : o ∈ pCoreOf p K) : k * o * k⁻¹ ∈ pCoreOf p K := by
  rw [pCoreOf] at ho ⊢
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem exists_ne_one_commute_of_normalizes {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]
    {P O : Subgroup X} [Finite O] (hP : IsPGroup p P) (hO : IsPGroup p O) (hO1 : O ≠ ⊥)
    (hn : ∀ g ∈ P, ∀ o ∈ O, g * o * g⁻¹ ∈ O) : ∃ o ∈ O, o ≠ 1 ∧ ∀ g ∈ P, g * o = o * g := by
  let _ : MulAction P O :=
    { smul := fun g o => ⟨(g : X) * o * (g : X)⁻¹, hn g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (by
        change ((1 : P) : X) * (o : X) * ((1 : P) : X)⁻¹ = o
        rw [coe_one, one_mul, inv_one, mul_one])
      mul_smul := fun a b o => Subtype.ext (by
        change ((a * b : P) : X) * (o : X) * ((a * b : P) : X)⁻¹ =
          (a : X) * ((b : X) * o * (b : X)⁻¹) * (a : X)⁻¹
        rw [coe_mul]
        group) }
  have h1 : (1 : O) ∈ MulAction.fixedPoints P O := fun g => Subtype.ext (by
    change (g : X) * 1 * (g : X)⁻¹ = 1
    group)
  have hdvd : p ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hO1 ((card_eq_one).mp hk)
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point O hdvd h1
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun g hg => ?_⟩
  have e : (g : X) * b * (g : X)⁻¹ = b := congrArg Subtype.val (hb ⟨g, hg⟩)
  calc g * (b : X) = g * b * g⁻¹ * g := by group
    _ = b * g := by rw [e]

variable {G : Type} [Group G] [Finite G]

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

omit [Finite G] in
theorem commutator_mem_zGen (htop : S.zGen ⊔ S.QG = ⊤) (a b : G) :
    a * b * a⁻¹ * b⁻¹ ∈ S.zGen := by
  have hLn := S.zGen_normal
  have key : ∀ k : G, ∃ q ∈ S.QG,
      QuotientGroup.mk' S.zGen k = QuotientGroup.mk' S.zGen q := by
    intro k
    obtain ⟨l, hl, q, hq, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := S.zGen)).mp (htop ▸ mem_top k)
    refine ⟨q, hq, ?_⟩
    rw [map_mul, show QuotientGroup.mk' S.zGen l = 1 from (QuotientGroup.eq_one_iff l).mpr hl,
      one_mul]
  obtain ⟨qa, hqa, ha⟩ := key a
  obtain ⟨qb, hqb, hb⟩ := key b
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
  have e : QuotientGroup.mk' S.zGen (a * b * a⁻¹ * b⁻¹) =
      QuotientGroup.mk' S.zGen (qa * qb * qa⁻¹ * qb⁻¹) := by
    simp only [map_mul, map_inv, ha, hb]
  rw [e, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rcases S.commutator_eq_one_or_z hqa hqb with h | h <;> rw [h]
  · exact one_mem _
  · exact S.z_mem_zGen

end ConfHyp

omit [Finite G] in
theorem Frame.mem_of_σ_eq_commutator (F : Frame G) {K : Subgroup G}
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) {a : F.A} {p q : Equiv.Perm (Fin 5)}
    (hp : p ∈ alternatingGroup (Fin 5)) (hq : q ∈ alternatingGroup (Fin 5))
    (h : F.σ a = p * q * p⁻¹ * q⁻¹) : (a : G) ∈ K := by
  obtain ⟨b, rfl⟩ := F.exists_σ_eq hp
  obtain ⟨c, rfl⟩ := F.exists_σ_eq hq
  have e : a = b * c * b⁻¹ * c⁻¹ := F.σ_injective (by rw [h]; simp only [map_mul, map_inv])
  rw [e]
  exact hK b c

namespace Gens

variable {S : Setting G} {H : Subgroup G} (g : Gens S H)

omit [Finite G] in
theorem mem_of_commutator_mem {K : Subgroup G} (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    g.e ∈ K ∧ g.x ∈ K ∧ g.s ∈ K := by
  obtain ⟨a, hae, ha⟩ := g.F.exists_A_eq_of_rep_vec_zero g.rep_e
  obtain ⟨b, hbx, hb⟩ := g.F.exists_A_eq_of_rep_vec_zero g.rep_x
  obtain ⟨c, hcs, hc⟩ := g.F.exists_A_eq_of_rep_vec_zero g.rep_s
  have hσa : g.F.σ a = Equiv.swap 1 2 * Equiv.swap 3 4 := permCode_injective (ha.trans (by decide))
  have hσb : g.F.σ b = Equiv.swap 2 3 * Equiv.swap 3 4 := permCode_injective (hb.trans (by decide))
  have hσc : g.F.σ c = Equiv.swap 0 1 * Equiv.swap 2 3 := permCode_injective (hc.trans (by decide))
  refine ⟨hae ▸ g.F.mem_of_σ_eq_commutator hK
      (Frame.mem_alternatingGroup_swap_mul_swap (a := 1) (b := 2) (c := 1) (d := 3) (by decide)
        (by decide))
      (Frame.mem_alternatingGroup_swap_mul_swap (a := 1) (b := 2) (c := 1) (d := 4) (by decide)
        (by decide)) (by rw [hσa]; decide),
    hbx ▸ g.F.mem_of_σ_eq_commutator hK
      (Frame.mem_alternatingGroup_swap_mul_swap (a := 0) (b := 1) (c := 2) (d := 3) (by decide)
        (by decide))
      (Frame.mem_alternatingGroup_swap_mul_swap (a := 0) (b := 1) (c := 2) (d := 4) (by decide)
        (by decide)) (by rw [hσb]; decide),
    hcs ▸ g.F.mem_of_σ_eq_commutator hK
      (Frame.mem_alternatingGroup_swap_mul_swap (a := 0) (b := 1) (c := 0) (d := 2) (by decide)
        (by decide))
      (Frame.mem_alternatingGroup_swap_mul_swap (a := 0) (b := 1) (c := 0) (d := 3) (by decide)
        (by decide)) (by rw [hσc]; decide)⟩

end Gens

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem le_zGen (hc : ConfHyp S H) (htop : S.zGen ⊔ S.QG = ⊤) : H ≤ S.zGen := by
  obtain ⟨g⟩ := hc.exists_gens
  obtain ⟨he, hx, hs⟩ := g.mem_of_commutator_mem (ConfHyp.commutator_mem_zGen htop)
  intro h hh
  obtain ⟨w, hw⟩ := g.Φ2_surjective hc ⟨h, hh⟩
  have e : h = PresentedGroup.toGroup (g.F.rels2_hold g.rep_z g.rep_t g.rep_e g.rep_x g.rep_s) w :=
    (congrArg Subtype.val hw).symm
  rw [e]
  exact Sem.toGroup_mem _ (Frame.gens2_mem S.z_mem_zGen
    (S.zConj_subset_zGen H g.t_mem_zConj) he hx hs) w

theorem zGen_eq_top (hc : ConfHyp S H) (htop : S.zGen ⊔ S.QG = ⊤) : S.zGen = ⊤ := by
  rw [← htop]
  exact (sup_eq_left.mpr (hc.QG_le.trans (hc.le_zGen htop))).symm

theorem isSimpleGroup (hc : ConfHyp S H) (htop : S.zGen ⊔ S.QG = ⊤)
    (hsimp : IsSimpleGroup S.zGen) : IsSimpleGroup G :=
  ((MulEquiv.subgroupCongr (hc.zGen_eq_top htop)).trans Subgroup.topEquiv).symm.isSimpleGroup

theorem exists_not_commute (hc : ConfHyp S H) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨g⟩ := hc.exists_gens
  exact ⟨g.s, S.z, fun h => g.s_not_mem_M (S.mem_M_iff.mpr h)⟩

theorem pCoreOf_sup_eq_bot (hc : ConfHyp S H) : pCoreOf 2 (S.M ⊔ H) = ⊥ := by
  obtain ⟨g⟩ := hc.exists_gens
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 (S.M ⊔ H) with hOdef
  have hOp : IsPGroup 2 O := isPGroup_pCoreOf 2 _
  have hOn : ∀ k ∈ S.M ⊔ H, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho => conj_mem_pCoreOf 2 hk ho
  have hOM : O ⊓ S.M ≤ S.QG := S.le_QG_of_normalizes' inf_le_right
    (fun c hcM o ho => ⟨hOn c (mem_sup_left hcM) o ho.1,
      S.M.mul_mem (S.M.mul_mem hcM ho.2) (S.M.inv_mem hcM)⟩) (hOp.to_le inf_le_left)
  have hzO : S.z ∉ O := by
    intro hz
    have htO := hOn g.s (mem_sup_right (g.mem_H g.rep_s)) S.z hz
    rw [g.isFrameOf.conj_z_of_rep_sD g.rep_s, ← g.t_eq] at htO
    exact hc.not_mem_QG g.t_mem_zConj g.t_ne_z (hOM ⟨htO, g.t_mem_M hc⟩)
  by_contra hne
  obtain ⟨o, hoO, ho1, hoc⟩ := exists_ne_one_commute_of_normalizes (P := S.QG)
    (S.extraspecial.1.map _) hOp hne fun q hq o ho => hOn q (mem_sup_left (S.QG_le_M hq)) o ho
  have hoM : o ∈ S.M := S.mem_M_iff.mpr (hoc S.z S.z_mem_QG).symm
  rcases S.eq_one_or_z_of_commute (hOM ⟨hoO, hoM⟩) (fun y hy => (hoc y hy).symm) with h | h
  · exact ho1 h
  · exact hzO (h ▸ hoO)

omit [Finite G] in
theorem z_mem_centerOf_inf (hc : ConfHyp S H) : S.z ∈ centerOf (S.M ⊓ H) :=
  ⟨hc.z_mem_inf, mem_centralizer_iff.mpr fun _ hh => S.z_comm hh.1⟩

end ConfHyp

omit [Finite G] in
theorem pCoreOf_M_eq_QG (S : Setting G) : pCoreOf 2 S.M = S.QG := by
  rw [pCoreOf, ← S.Q_eq_pCore]
  rfl

omit [Finite G] in
theorem mem_centerOf_QG_iff (S : Setting G) {x : G} : x ∈ centerOf S.QG ↔ x = 1 ∨ x = S.z := by
  constructor
  · rintro ⟨hx, hxc⟩
    exact S.eq_one_or_z_of_commute hx fun y hy => (mem_centralizer_iff.mp hxc y hy).symm
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact ⟨S.z_mem_QG, mem_centralizer_iff.mpr fun _ hy => S.z_comm_QG hy⟩

omit [Finite G] in
theorem normalizer_centerOf_pCoreOf_M (S : Setting G) :
    normalizer (centerOf (pCoreOf 2 S.M) : Set G) = S.M := by
  rw [pCoreOf_M_eq_QG]
  ext k
  rw [mem_normalizer_iff]
  constructor
  · intro h
    rcases (mem_centerOf_QG_iff S).mp ((h S.z).mp ((mem_centerOf_QG_iff S).mpr (Or.inr rfl)))
      with h1 | h1
    · exact absurd (conj_eq_one_iff.mp h1) S.z_ne_one
    · exact S.mem_M_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1)
  · intro hk x
    have e := S.conj_z_of_mem_M hk
    rw [mem_centerOf_QG_iff, mem_centerOf_QG_iff]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl (by group)
      · exact Or.inr e
    · rintro (h1 | h1)
      · exact Or.inl (conj_eq_one_iff.mp h1)
      · rw [← e] at h1
        exact Or.inr (by simpa using h1)

end AS62

end CFSG.LargeExtraspecial
