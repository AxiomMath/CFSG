module

public import CFSG.LocalAnalysis.EvenBN.G2.Setup
public import CFSG.LocalAnalysis.EvenBN.G2.Torus

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_center_of_mem_normalizer {R : Subgroup G} {n z : G}
    (hn : n ∈ normalizer (R : Set G)) (hz : z ∈ R) (hzc : ∀ r ∈ R, z * r = r * z) :
    n * z * n⁻¹ ∈ R ∧ ∀ r ∈ R, n * z * n⁻¹ * r = r * (n * z * n⁻¹) := by
  refine ⟨(mem_normalizer_iff.1 hn z).1 hz, fun r hr => ?_⟩
  have hr' : n⁻¹ * r * n ∈ R := by
    have := (mem_normalizer_iff.1 (inv_mem hn) r).1 hr
    simpa using this
  have h1 := hzc _ hr'
  calc n * z * n⁻¹ * r = n * (z * (n⁻¹ * r * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * r * n) * z) * n⁻¹ := by rw [h1]
    _ = r * (n * z * n⁻¹) := by group

theorem mem_normalizer_of_conj_mem {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hinj : Function.Injective (fun x : H => (⟨g * x * g⁻¹, h x x.2⟩ : H)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.1 hinj
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  obtain ⟨k, hk⟩ := hsurj ⟨g * n * g⁻¹, hn⟩
  have hkn : (k : G) = n := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← hkn]
  exact k.2

variable [Finite G]

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {T H X : Subgroup G}
    (hT : IsSylowOf p T H) (hXH : X ≤ H) (hX : IsPGroup p X) :
    ∃ c ∈ H, ∀ x ∈ X, c⁻¹ * x * c ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXH hx⟩ : H) ∈ (Q : Subgroup H) := hQ hx
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  refine ⟨s, hs, ?_⟩
  have : (c : G) * s * (c : G)⁻¹ = x := by
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [Subgroup.subtype_apply, ← this]
  group

end Generic

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

@[expose] noncomputable def xv : G :=
  d.emb ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩

@[expose] noncomputable def xc : G :=
  d.emb ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩

section Facts

variable
  [CharP K 2]

theorem xv_xc_spec :
    d.xv ∈ d.W ∧ d.xv ∉ d.Y ∧ d.xv * d.xv = 1 ∧ d.xc ∈ d.U ∧ d.xc ≠ 1 ∧ d.xc * d.xc = 1 := by
  have hv : pinnedX .G2 K g2v 1 ∈ Model.W K := by
    rw [pinnedX_v_eq_g2N]
    exact Model.g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩
  have hvY : pinnedX .G2 K g2v 1 ∉ Model.Y K := by
    rw [pinnedX_v_eq_g2N, Model.g2N_mem_Y_iff]
    exact fun h => one_ne_zero h.2.2.2
  have hsq : ∀ s : Fin Tag.G2.rank → ℤ,
      d.emb ⟨pinnedX .G2 K s 1, pinnedX_mem_adjointGroup s 1⟩ *
        d.emb ⟨pinnedX .G2 K s 1, pinnedX_mem_adjointGroup s 1⟩ = 1 := fun s => by
    rw [← map_mul, ← map_one d.emb]
    refine congrArg d.emb (Subtype.ext ?_)
    rw [coe_mul, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero, coe_one]
  refine ⟨d.emb_mem_image hv, fun h => hvY (d.emb_mem_image_iff.1 h), hsq g2v,
    d.emb_mem_image (mem_rootSubgroup.2 ⟨1, rfl⟩), fun h1 => ?_, hsq g2c⟩
  have h2 : pinnedX .G2 K g2c 1 = 1 :=
    congrArg Subtype.val (d.emb_injective (h1.trans (map_one d.emb).symm))
  rw [pinnedX_c_eq_g2N, ← g2N_zero] at h2
  exact one_ne_zero (g2N_injective h2).2.2.2.2.2

theorem exists_conj_U [Finite K] {u u' : G} (hu : u ∈ d.U) (hu1 : u ≠ 1) (hu' : u' ∈ d.U)
    (hu'1 : u' ≠ 1) : ∃ j ∈ L ⊓ normalizer (d.S : Set G), j * u * j⁻¹ = u' := by
  obtain ⟨x, hx, rfl⟩ := d.mem_image.1 hu
  obtain ⟨y, hy, rfl⟩ := d.mem_image.1 hu'
  have hx1 : (x : ModGL .G2 K) ≠ 1 := fun h1 =>
    hu1 (by rw [show x = 1 from Subtype.ext h1, map_one])
  have hy1 : (y : ModGL .G2 K) ≠ 1 := fun h1 =>
    hu'1 (by rw [show y = 1 from Subtype.ext h1, map_one])
  have hik : Model.Ji K 1 ⊓ Model.Ji K 0 = ⊥ :=
    Model.Ji_inf_Ji_eq_bot (by decide) (Or.inr (by decide))
  obtain ⟨j, hj, hjxy⟩ := Model.exists_Ji_conj_eq hik hx hx1 hy hy1
  have hJ : Model.Ji K 1 ≤ adjointGroup .G2 K ⊓ normalizer (Model.S K : Set (ModGL .G2 K)) := by
    rw [(Model.yamada_3_13_1 (K := K)).2.2]
    exact inf_le_left.trans le_sup_left
  refine ⟨d.emb ⟨j, (hJ hj).1⟩, ?_, ?_⟩
  · rw [G2Data.S, ← d.image_inf_normalizer (Model.S_le_adjointGroup K)]
    exact d.emb_mem_image (hJ hj)
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext hjxy)

theorem exists_conj_xv [Finite K] {w : G} (hw : w ∈ d.W) (hwY : w ∉ d.Y) :
    ∃ n ∈ L ⊓ normalizer (d.W : Set G), n * w * n⁻¹ = d.xv := by
  obtain ⟨w₀, hw₀, rfl⟩ := d.mem_image.1 hw
  have hwY₀ : (w₀ : ModGL .G2 K) ∉ Model.Y K := fun h => hwY (d.emb_mem_image h)
  obtain ⟨D, E, F, hDEF⟩ := Model.mem_W.1 hw₀
  have hD : D ≠ 0 := by
    rintro rfl
    rw [hDEF] at hwY₀
    exact hwY₀ (Model.g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩)
  have h1 : pinnedX .G2 K g2r (E / D) * g2N 0 0 0 D E F * (pinnedX .G2 K g2r (E / D))⁻¹ =
      g2N 0 0 0 D 0 F := by
    rw [pinnedX_r_eq_g2N, g2N_conj_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mul_zero, zero_mul, add_zero, zero_add, zero_pow two_ne_zero,
      zero_pow (three_ne_zero (α := ℕ))]
    rw [div_mul_cancel₀ E hD, CharTwo.add_self_eq_zero]
  have h2 : pinnedX .G2 K g2u (F / D) * g2N 0 0 0 D 0 F * (pinnedX .G2 K g2u (F / D))⁻¹ =
      g2N 0 0 0 D 0 0 := by
    rw [pinnedX_u_eq_g2N, g2N_conj_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mul_zero, zero_mul, add_zero, zero_add, zero_pow two_ne_zero,
      zero_pow (three_ne_zero (α := ℕ))]
    rw [div_mul_cancel₀ F hD, CharTwo.add_self_eq_zero]
  have hik : Model.Ji K 3 ⊓ Model.Ji K 1 = ⊥ :=
    Model.Ji_inf_Ji_eq_bot (by decide) (Or.inr (by decide))
  have hne : ∀ c : K, c ≠ 0 → pinnedX .G2 K g2v c ≠ 1 := fun c hc h1 => by
    rw [pinnedX_v_eq_g2N, ← g2N_zero] at h1
    exact hc (g2N_injective h1).2.2.2.1
  obtain ⟨n₃, hn₃, h3⟩ := Model.exists_Ji_conj_eq hik (mem_rootSubgroup.2 ⟨D, rfl⟩) (hne D hD)
    (mem_rootSubgroup.2 ⟨1, rfl⟩) (hne 1 one_ne_zero)
  have hNW := (Model.yamada_3_13_3 (K := K)).2.1
  have hSN : ∀ x ∈ Model.S K, x ∈ adjointGroup .G2 K ⊓ normalizer (Model.W K : Set _) :=
    fun x hx => ⟨Model.S_le_adjointGroup K hx, Model.S_le_normalizer_W hx⟩
  have hn₁ : pinnedX .G2 K g2r (E / D) ∈ adjointGroup .G2 K ⊓ normalizer (Model.W K : Set _) :=
    hSN _ (Model.rootSubgroup_yamadaRoot_le_S 2 (mem_rootSubgroup.2 ⟨E / D, rfl⟩))
  have hn₂ : pinnedX .G2 K g2u (F / D) ∈ adjointGroup .G2 K ⊓ normalizer (Model.W K : Set _) :=
    hSN _ (Model.rootSubgroup_yamadaRoot_le_S 5 (mem_rootSubgroup.2 ⟨F / D, rfl⟩))
  have hn₃' : n₃ ∈ adjointGroup .G2 K ⊓ normalizer (Model.W K : Set _) := by
    rw [hNW]
    exact mem_sup_right (mem_sup_right hn₃)
  have hn := mul_mem (mul_mem hn₃' hn₂) hn₁
  refine ⟨d.emb ⟨_, hn.1⟩, ?_, ?_⟩
  · rw [G2Data.W, ← d.image_inf_normalizer Model.W_le_adjointGroup]
    exact d.emb_mem_image hn
  · rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg d.emb (Subtype.ext ?_)
    simp only [coe_mul, coe_inv]
    rw [hDEF]
    calc n₃ * pinnedX .G2 K g2u (F / D) * pinnedX .G2 K g2r (E / D) * g2N 0 0 0 D E F *
          (n₃ * pinnedX .G2 K g2u (F / D) * pinnedX .G2 K g2r (E / D))⁻¹ =
        n₃ * (pinnedX .G2 K g2u (F / D) * (pinnedX .G2 K g2r (E / D) * g2N 0 0 0 D E F *
          (pinnedX .G2 K g2r (E / D))⁻¹) * (pinnedX .G2 K g2u (F / D))⁻¹) * n₃⁻¹ := by group
      _ = n₃ * pinnedX .G2 K g2v D * n₃⁻¹ := by rw [h1, h2, pinnedX_v_eq_g2N]
      _ = pinnedX .G2 K g2v 1 := h3

theorem leviB_spec [Finite K] :
    (∀ l ∈ d.leviB, l * d.xv = d.xv * l) ∧ d.leviB ≤ normalizer (d.W : Set G) := by
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨l₀, hl₀, rfl⟩ := d.mem_image.1 hl
    have hc := (commute_of_mem_g2RankOne_a hl₀ 1).eq
    rw [xv, ← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext hc)
  · have h1 : d.leviB ≤ L ⊓ normalizer (d.W : Set G) := by
      rw [(d.yamada_3_13_3_G (K := K)).2.1]
      exact le_sup_left.trans le_sup_right
    exact h1.trans inf_le_right

theorem leviB_perfect [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅d.leviB, d.leviB⁆ = d.leviB ∧ d.leviB ≠ ⊥ := by
  have hB := Model.leviB_le_adjointGroup K
  refine ⟨?_, fun hbot => ?_⟩
  · rw [G2Data.leviB, ← d.image_commutator hB hB]
    exact congrArg d.image (g2RankOne_commutator hK)
  · have hmem : pinnedX .G2 K g2a 1 ∈ Model.leviB K := by
      rw [← xUnit_g2ia]
      exact xUnit_mem_g2RankOne g2ia 1
    have h1 := d.emb_mem_image (g := ⟨_, pinnedX_mem_adjointGroup g2a 1⟩) hmem
    rw [← G2Data.leviB, hbot, mem_bot, ← map_one d.emb] at h1
    have h2 : pinnedX .G2 K g2a 1 = 1 := congrArg Subtype.val (d.emb_injective h1)
    rw [pinnedX_a_eq_g2N, ← g2N_zero] at h2
    exact one_ne_zero (g2N_injective h2).2.1

theorem eq_bot_of_le_normalizer_X [Finite K] [Finite G] {P : Subgroup G} (hPL : P ≤ L)
    (hP : ⁅P, P⁆ = P) (hPX : P ≤ normalizer (d.X : Set G)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJS : d.J ⊔ d.S = d.image (Model.J K ⊔ Model.S K) :=
    (d.image_sup (Model.J_le_adjointGroup K) (Model.S_le_adjointGroup K)).symm
  have hJSA : Model.J K ⊔ Model.S K ≤ adjointGroup .G2 K :=
    sup_le (Model.J_le_adjointGroup K) (Model.S_le_adjointGroup K)
  have hB : borelGroup .G2 K = Model.J K ⊔ Model.S K := by
    rw [← Model.adjointGroup_inf_normalizer_X, (Model.yamada_3_13_1 (K := K)).1]
  have hPJS : P ≤ d.J ⊔ d.S := by
    rw [← (d.yamada_3_13_1_G).1]
    exact le_inf hPL hPX
  have hPS : P ≤ d.S := by
    rw [← hP]
    refine (commutator_mono hPJS hPJS).trans ?_
    rw [hJS, ← d.image_commutator hJSA hJSA, ← hB, G2Data.S]
    exact d.image_mono Model.commutator_borelGroup_le
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  have hperf : Group.IsPerfect P := by
    rw [Group.isPerfect_def]
    apply Subgroup.map_injective P.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hP]
  exact CFSG.ComponentClassification.AS81.G2.not_isPGroup_of_isPerfect hperf
    (d.isSylowOf_S.isPGroup.to_le hPS)

theorem exists_conj_xc_or_xv [Finite K] {l : G} (hl : l ∈ L) (hl2 : orderOf l = 2) :
    ∃ m ∈ L, m * l * m⁻¹ = d.xc ∨ m * l * m⁻¹ = d.xv := by
  obtain ⟨l₀, rfl⟩ := d.exists_emb_eq hl
  have hl₀ : orderOf l₀ = 2 := by rw [← orderOf_injective d.emb d.emb_injective]; exact hl2
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) l₀ hl₀ with hc | hc
  · obtain ⟨m, hm⟩ := isConj_iff.1 hc
    refine ⟨d.emb m, d.emb_mem m, Or.inl ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hm]
    rfl
  · obtain ⟨m, hm⟩ := isConj_iff.1 hc
    refine ⟨d.emb m, d.emb_mem m, Or.inr ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hm]
    rfl

theorem exists_xv_mul_xv [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ v₁ v₂ y : G, v₁ ∈ d.W ∧ v₁ ∉ d.Y ∧ v₂ ∈ d.W ∧ v₂ ∉ d.Y ∧ v₁ * v₂ = d.xv ∧
      y ∈ d.Y ∧ y ≠ 1 ∧ d.xc * y ≠ 1 := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  have hω1' : 1 + ω ≠ 0 := fun h0 => hω1 (by
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
    exact h0)
  have hW : ∀ c : K, d.emb ⟨pinnedX .G2 K g2v c, pinnedX_mem_adjointGroup g2v c⟩ ∈ d.W := fun c =>
    d.emb_mem_image (show pinnedX .G2 K g2v c ∈ Model.W K by
      rw [pinnedX_v_eq_g2N]; exact Model.g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩)
  have hY : ∀ c : K, c ≠ 0 →
      d.emb ⟨pinnedX .G2 K g2v c, pinnedX_mem_adjointGroup g2v c⟩ ∉ d.Y := fun c hc h1 => by
    have h2 : pinnedX .G2 K g2v c ∈ Model.Y K := d.emb_mem_image_iff.1 h1
    rw [pinnedX_v_eq_g2N, Model.g2N_mem_Y_iff] at h2
    exact hc h2.2.2.2
  have hmul : ∀ (s : Fin Tag.G2.rank → ℤ) (c₁ c₂ : K),
      d.emb ⟨pinnedX .G2 K s c₁, pinnedX_mem_adjointGroup s c₁⟩ *
        d.emb ⟨pinnedX .G2 K s c₂, pinnedX_mem_adjointGroup s c₂⟩ =
      d.emb ⟨pinnedX .G2 K s (c₁ + c₂), pinnedX_mem_adjointGroup s (c₁ + c₂)⟩ := fun s c₁ c₂ => by
    rw [← map_mul]
    exact congrArg d.emb (Subtype.ext (show pinnedX .G2 K s c₁ * pinnedX .G2 K s c₂ =
      pinnedX .G2 K s (c₁ + c₂) from (pinnedX_add _ _ _ _ _).symm))
  have hcongr : ∀ (s : Fin Tag.G2.rank → ℤ) (c c' : K), c = c' →
      d.emb ⟨pinnedX .G2 K s c, pinnedX_mem_adjointGroup s c⟩ =
        d.emb ⟨pinnedX .G2 K s c', pinnedX_mem_adjointGroup s c'⟩ := by
    rintro s c c' rfl
    rfl
  have hc1 : ∀ c : K, c ≠ 0 →
      d.emb ⟨pinnedX .G2 K g2c c, pinnedX_mem_adjointGroup g2c c⟩ ≠ 1 := fun c hc h1 => by
    have h2 : pinnedX .G2 K g2c c = 1 :=
      congrArg Subtype.val (d.emb_injective (h1.trans (map_one d.emb).symm))
    rw [pinnedX_c_eq_g2N, ← g2N_zero] at h2
    exact hc (g2N_injective h2).2.2.2.2.2
  have hcU : d.emb ⟨pinnedX .G2 K g2c ω, pinnedX_mem_adjointGroup g2c ω⟩ ∈ d.U :=
    d.emb_mem_image (show pinnedX .G2 K g2c ω ∈ Model.U K from mem_rootSubgroup.2 ⟨ω, rfl⟩)
  refine ⟨_, _, _, hW ω, hY ω hω0, hW (1 + ω), hY (1 + ω) hω1', ?_, (d.inclusions).1 hcU,
    hc1 ω hω0, ?_⟩
  · rw [hmul, xv]
    refine hcongr _ _ _ ?_
    rw [← add_assoc, add_comm ω 1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [xc, hmul]
    exact hc1 _ hω1'

end Facts

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem zpow_eq_one_or_eq (h : Setup G L f t) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have hk : t ^ k = t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.ht]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero]
  · right
    rw [hk, h1, zpow_one]

theorem mem_sup_zpowers_iff (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L) {x : G} :
    x ∈ E ⊔ zpowers t ↔ x ∈ E ∨ t * x ∈ E := by
  have hcomm : ∀ e ∈ E, ∀ y ∈ zpowers t, e * y = y * e := fun e he y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL e (hEL he) : Commute e t) k).eq
  constructor
  · intro hx
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers t) hcomm).2
    have hx' : x ∈ ((E ⊔ zpowers t : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨e, he, y, hy, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    beta_reduce
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · left
      rw [hk, mul_one]
      exact he
    · right
      rw [hk, hcomm e he t (mem_zpowers t), ← mul_assoc, h.t_mul_t, one_mul]
      exact he
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx)

theorem mem_or_mul_mem_of_mem_sup_kernel (h : Setup G L f t) {x : G}
    (hx : x ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) (hx2 : x * x = 1) :
    x ∈ L ∨ t * x ∈ L := by
  have hx' : x ∈ ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) :
      Set G) := hx
  rw [h.coe_sup_kernel] at hx'
  obtain ⟨l, hl, c, hc, rfl⟩ := hx'
  beta_reduce at hx2 ⊢
  have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
  have hcL : c ∈ centralizer (L : Set G) := (Subgroup.mem_inf.1 hc').1
  have hlc : l * c = c * l := mem_centralizer_iff.1 hcL l hl
  have hll : l * l * (c * c) = 1 := by
    rw [← hx2]
    calc l * l * (c * c) = l * (l * c) * c := by group
      _ = l * (c * l) * c := by rw [hlc]
      _ = l * c * (l * c) := by group
  have hc2 : c * c = 1 := by
    have hmem : l * l ∈ L ⊓ centralizer (L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem hl hl, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hll]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hcL hcL)
    rw [h.inf_centralizer_eq_bot, mem_bot] at hmem
    rwa [hmem, one_mul] at hll
  by_cases hc1 : c = 1
  · left
    rw [hc1, mul_one]
    exact hl
  · right
    have hct : c = t := h.kernel.2.2.1 c hc' (orderOf_eq_prime (by rw [sq]; exact hc2) hc1)
    rw [hct] at hlc ⊢
    rw [hlc, ← mul_assoc, h.t_mul_t, one_mul]
    exact hl

section Main

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem conj_mem_yamadaR (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({t} : Set G))
    (hRQ : yamadaR d t ≤ Q) {c : G} (hc : ∀ r ∈ yamadaR d t, c⁻¹ * r * c ∈ Q) :
    ∀ r ∈ yamadaR d t, c⁻¹ * r * c ∈ yamadaR d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (yamadaR d t) := (h.isSylowOf_yamadaR d).isPGroup
  have hRC := h.yamadaR_le_centralizer d
  have hJR := h.rankThompson_eq d hK hR2 hRC le_rfl
  have hJQ := h.rankThompson_eq d hK hQ2 hQC hRQ
  have hrR := h.pRank_eq d hK hRC le_rfl
  have hrQ := h.pRank_eq d hK hQC hRQ
  suffices hle : yamadaR d t ≤ (yamadaR d t).comap (MulAut.conj c⁻¹).toMonoidHom by
    intro r hr
    have := hle hr
    simpa [mem_comap, MulAut.conj_apply] using this
  conv_lhs => rw [← hJR]
  refine iSup₂_le fun A ⟨hAR, hA, hrA⟩ => ?_
  rw [← map_le_iff_le_comap, ← hJQ]
  have hAQ : A.map (MulAut.conj c⁻¹).toMonoidHom ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hc a (hAR ha)
  refine le_iSup₂_of_le (A.map (MulAut.conj c⁻¹).toMonoidHom) ⟨hAQ, ?_, ?_⟩ le_rfl
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b₀, hb₀, hb⟩ := Subgroup.mem_map.1 b.2
    change (a : G) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨a₀, ha₀⟩ : A) ⟨b₀, hb₀⟩))
  · refine le_antisymm (SectionRank.pRank_mono one_lt_two hAQ) ?_
    rw [hrQ, ← hrR, ← hrA]
    exact SectionRank.pRank_le_map one_lt_two _ (MulAut.conj c⁻¹).injective A

omit [Finite K] in
theorem exists_mul_of_mem_center_yamadaR (_h : Setup G L f t) (d : G2Data L K) {z : G}
    (hz : z ∈ yamadaR d t) (hzc : ∀ r ∈ yamadaR d t, z * r = r * z) :
    ∃ u ∈ d.U, ∃ c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), z = u * c := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).2
  have hz' : z ∈ ((yamadaR d t : Subgroup G) : Set G) := hz
  rw [yamadaR, hset] at hz'
  obtain ⟨s, hs, c, hc, rfl⟩ := hz'
  beta_reduce at hzc ⊢
  refine ⟨s, ?_, c, hc, rfl⟩
  rw [← (d.yamada_3_12_centers).1]
  refine Subgroup.mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun r hr => ?_⟩
  have h1 := hzc r (mem_sup_left hr)
  have h2 : r * c = c * r := S_commute_kernel d t r hr c hc
  have h3 : s * r * c = r * s * c := by
    calc s * r * c = s * (r * c) := by group
      _ = s * (c * r) := by rw [h2]
      _ = s * c * r := by group
      _ = r * (s * c) := h1
      _ = r * s * c := by group
  exact (mul_right_cancel h3).symm

theorem exists_conj_eq_mul_of_mem_normalizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {n : G} (hn : n ∈ normalizer (yamadaR d t : Set G)) :
    ∃ u ∈ d.U, n * t * n⁻¹ = t * u := by
  have htR : t ∈ yamadaR d t := mem_sup_right h.t_mem_kernel
  have htc : ∀ r ∈ yamadaR d t, r * t = t * r := fun r hr =>
    mem_centralizer_singleton_iff.1 (h.yamadaR_le_centralizer d hr)
  have hzR : n * t * n⁻¹ ∈ yamadaR d t := (mem_normalizer_iff.1 hn t).1 htR
  have hzc : ∀ r ∈ yamadaR d t, n * t * n⁻¹ * r = r * (n * t * n⁻¹) := by
    intro r hr
    have hr' : n⁻¹ * r * n ∈ yamadaR d t := by
      have := (mem_normalizer_iff.1 (inv_mem hn) r).1 hr
      simpa using this
    have h1 := htc _ hr'
    calc n * t * n⁻¹ * r = n * (t * (n⁻¹ * r * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * r * n) * t) * n⁻¹ := by rw [h1]
      _ = r * (n * t * n⁻¹) := by group
  obtain ⟨u, hu, c, hc, hzuc⟩ := h.exists_mul_of_mem_center_yamadaR d hzR hzc
  have huL : u ∈ L := d.image_le _ hu
  have huc : u * c = c * u := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1 u huL
  have hu2 : u * u = 1 := by
    have := d.isElementaryAbelian.1
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.U) u hu
    rwa [sq] at this
  have hz2 : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]
  have hc2 : c * c = 1 := by
    rw [hzuc] at hz2
    calc c * c = u * u * (c * c) := by rw [hu2, one_mul]
      _ = u * (u * c) * c := by group
      _ = u * (c * u) * c := by rw [huc]
      _ = u * c * (u * c) := by group
      _ = 1 := hz2
  by_cases hc1 : c = 1
  · exfalso
    rw [hc1, mul_one] at hzuc
    exact h.conj_not_mem_Y d hK n (hzuc ▸ (d.inclusions).1 hu)
  · have hct : c = t := h.kernel.2.2.1 c hc (orderOf_eq_prime (by rw [sq]; exact hc2) hc1)
    refine ⟨u, hu, ?_⟩
    rw [hzuc, hct]
    exact (mem_centralizer_singleton_iff.1 (h.L_le_centralizer huL))

omit
  [Finite K] [CharP K 2] in
theorem inf_normalizer_le_normalizer_yamadaR (_h : Setup G L f t) (d : G2Data L K) :
    L ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaR d t : Set G) := by
  refine le_normalizer_of_conj_mem fun j hj r hr => ?_
  obtain ⟨hjL, hjS⟩ := Subgroup.mem_inf.1 hj
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).2
  have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
  rw [yamadaR, hset] at hr'
  obtain ⟨s, hs, c, hc, rfl⟩ := hr'
  beta_reduce
  have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
  have hjc : j * c = c * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 j hjL
  have e : j * (s * c) * j⁻¹ = j * s * j⁻¹ * c := by
    calc j * (s * c) * j⁻¹ = j * s * (j⁻¹ * (j * c)) * j⁻¹ := by group
      _ = j * s * (j⁻¹ * (c * j)) * j⁻¹ := by rw [hjc]
      _ = j * s * j⁻¹ * c := by group
  rw [e]
  exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hjS s).1 hs)) (mem_sup_right hc')

theorem conj_set_normalizer_yamadaR (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {n : G} (hn : n ∈ normalizer (yamadaR d t : Set G))
    (hnt : n * t * n⁻¹ ≠ t) :
    {x | ∃ m ∈ normalizer (yamadaR d t : Set G), m * t * m⁻¹ = x} =
      (fun u => t * u) '' (d.U : Set G) := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨u, hu, hmu⟩ := h.exists_conj_eq_mul_of_mem_normalizer d hK hm
    exact ⟨u, hu, hmu.symm⟩
  · rintro ⟨u', hu', rfl⟩
    obtain ⟨u, hu, hnu⟩ := h.exists_conj_eq_mul_of_mem_normalizer d hK hn
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [mul_one] at hnu
      exact hnt hnu
    by_cases hu'1 : u' = 1
    · exact ⟨1, one_mem _, by rw [hu'1]; group⟩
    · obtain ⟨j, hj, hju⟩ := d.exists_conj_U hu hu1 hu' hu'1
      refine ⟨j * n, mul_mem (h.inf_normalizer_le_normalizer_yamadaR d hj) hn, ?_⟩
      have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
        (h.L_le_centralizer (Subgroup.mem_inf.1 hj).1)
      calc j * n * t * (j * n)⁻¹ = j * (n * t * n⁻¹) * j⁻¹ := by group
        _ = j * t * u * j⁻¹ := by rw [hnu]; group
        _ = t * (j * u * j⁻¹) := by rw [hjt]; group
        _ = t * u' := by rw [hju]

theorem exists_isSylowOf_le (h : Setup G L f t) (d : G2Data L K) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (centralizer ({t} : Set G)) ∧ yamadaR d t ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC := h.yamadaR_le_centralizer d
  have hR2 : IsPGroup 2 ((yamadaR d t).subgroupOf (centralizer ({t} : Set G))) :=
    (h.isSylowOf_yamadaR d).isPGroup.comap_subtype
  obtain ⟨Q, hQ⟩ := hR2.exists_le_sylow
  refine ⟨(Q : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype,
    ⟨Q, rfl⟩, fun r hr => ⟨⟨r, hRC hr⟩, hQ (mem_subgroupOf.2 hr), rfl⟩⟩

theorem exists_normalizer_yamadaR_conj_eq (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {g : G}
    (hy : ∀ r ∈ yamadaR d t, r * (g * t * g⁻¹) = g * t * g⁻¹ * r) :
    ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = g * t * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y := g * t * g⁻¹ with hydef
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  have hC : (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({y} : Set G) := by
    ext z
    rw [mem_map_conj_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hz
      calc z * y = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by rw [hydef]; group
        _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [hz]
        _ = y * z := by rw [hydef]; group
    · intro hz
      calc g⁻¹ * z * g * t = g⁻¹ * (z * y) * g := by rw [hydef]; group
        _ = g⁻¹ * (y * z) * g := by rw [hz]
        _ = t * (g⁻¹ * z * g) := by rw [hydef]; group
  have hQ' : IsSylowOf 2 (Q.map (MulAut.conj g).toMonoidHom) (centralizer ({y} : Set G)) := by
    obtain ⟨hle, hP, hdvd⟩ := isSylowOf_iff.1 hQ
    refine isSylowOf_iff.2 ⟨?_, hP.map _, ?_⟩
    · rw [← hC]
      exact Subgroup.map_mono hle
    · rw [← hC, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hdvd
  have hRy : yamadaR d t ≤ centralizer ({y} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.2 (hy r hr)
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hQ' hRy (h.isSylowOf_yamadaR d).isPGroup
  have hcgQ : ∀ r ∈ yamadaR d t, (c * g)⁻¹ * r * (c * g) ∈ Q := by
    intro r hr
    have h1 := hc r hr
    rw [mem_map_conj_iff] at h1
    rwa [show g⁻¹ * (c⁻¹ * r * c) * g = (c * g)⁻¹ * r * (c * g) by group] at h1
  have hcgR := h.conj_mem_yamadaR d hK hQ.isPGroup hQ.le hRQ hcgQ
  have hN : (c * g)⁻¹ ∈ normalizer (yamadaR d t : Set G) :=
    mem_normalizer_of_conj_mem fun r hr => by
      rw [inv_inv]
      exact hcgR r hr
  refine ⟨c * g, by simpa using inv_mem hN, ?_⟩
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hcC
  calc c * g * t * (c * g)⁻¹ = c * y * c⁻¹ := by rw [hydef]; group
    _ = y := by rw [hcy]; group

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
