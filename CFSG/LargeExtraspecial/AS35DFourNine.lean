module

public import CFSG.LargeExtraspecial.AS35DFourSeven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

@[expose] def tiR (g : G) : Subgroup G := S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)

@[expose] noncomputable def tiP (g : G) : Subgroup G := S.Qa g ⊓ S.M

@[expose] noncomputable def tiS (g : G) : Subgroup G :=
  S.QG ⊓ normalizer ((S.tiR g ⊔ S.tiP g : Subgroup G) : Set G)

variable [Finite G]

omit [Finite G] in
theorem mem_inf_centralizer_iff_conj {x y : G} :
    y ∈ S.QG ⊓ centralizer ({x} : Set G) ↔ y ∈ S.QG ∧ x * y * x⁻¹ = y := by
  rw [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← h2]; group⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc y * x = (x * y * x⁻¹) * x := by rw [h2]
      _ = x * y := by group

theorem mem_clPre_fixSpace_iff {x : G} (hxM : x ∈ S.M) {y : G} (hy : y ∈ S.QG) :
    y ∈ S.clPre (fixSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ↔
      x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y * S.z := by
  rw [mem_clPre, mem_fixSpace, S.ρ_cl ⟨x, hxM⟩ hy]
  change y ∈ S.QG ∧ S.cl (x * y * x⁻¹) = S.cl y ↔ _
  rw [eq_comm, S.cl_eq_cl_iff hy (S.conj_mem_QG hxM hy)]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

theorem centralizer_le_clPre_fixSpace {x : G} (hxM : x ∈ S.M) :
    S.QG ⊓ centralizer ({x} : Set G) ≤
      S.clPre (fixSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := fun _ hy =>
  ((S.mem_clPre_fixSpace_iff hxM (S.mem_inf_centralizer_iff_conj.mp hy).1).mpr
    (Or.inl (S.mem_inf_centralizer_iff_conj.mp hy).2))

theorem card_clPre_fixSpace_le {x : G} (hxM : x ∈ S.M) :
    Nat.card (S.clPre (fixSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) ≤
      2 * Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  set P := S.clPre (fixSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) with hP
  set C := S.QG ⊓ centralizer ({x} : Set G) with hC
  have hmemP : ∀ y ∈ S.QG, y ∈ P ↔ x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y * S.z := fun y hy =>
    S.mem_clPre_fixSpace_iff hxM hy
  have hmemC : ∀ y, y ∈ C ↔ y ∈ S.QG ∧ x * y * x⁻¹ = y := fun y =>
    S.mem_inf_centralizer_iff_conj
  have hCP : C ≤ P := S.centralizer_le_clPre_fixSpace hxM
  by_cases hCeq : P ≤ C
  · have := Subgroup.card_le_of_le hCeq
    omega
  obtain ⟨y₀, hy₀P, hy₀C⟩ := Set.not_subset.mp hCeq
  have hy₀Q : y₀ ∈ S.QG := (S.mem_clPre.mp hy₀P).1
  have hy₀ : x * y₀ * x⁻¹ = y₀ * S.z :=
    ((hmemP y₀ hy₀Q).mp hy₀P).resolve_left fun h => hy₀C ((hmemC y₀).mpr ⟨hy₀Q, h⟩)
  have hrel : (C.subgroupOf P).index = 2 := by
    change C.relIndex P = 2
    rw [relIndex_eq_two_iff]
    refine ⟨y₀, hy₀P, fun b hbP => xor_iff_iff_not.mpr ?_⟩
    have hbQ : b ∈ S.QG := (S.mem_clPre.mp hbP).1
    have hconj : x * (b * y₀) * x⁻¹ = (x * b * x⁻¹) * (y₀ * S.z) := by
      rw [← hy₀]
      group
    rw [hmemC, hmemC, hconj]
    constructor
    · rintro ⟨-, h1⟩ ⟨-, h2⟩
      rw [h2] at h1
      apply S.z_ne_one
      calc S.z = (b * y₀)⁻¹ * (b * (y₀ * S.z)) := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      refine ⟨S.QG.mul_mem hbQ hy₀Q, ?_⟩
      have hb : x * b * x⁻¹ = b * S.z :=
        ((hmemP b hbQ).mp hbP).resolve_left fun h => h1 ⟨hbQ, h⟩
      rw [hb, show b * S.z * (y₀ * S.z) = b * (S.z * y₀) * S.z by group,
        ← S.z_comm_QG hy₀Q, mul_assoc, mul_assoc, S.z_mul_z, mul_one]
  have hcard := Subgroup.card_mul_index (C.subgroupOf P)
  rw [hrel, Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv] at hcard
  omega

theorem two_pow_width_le_card_centralizer {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1) :
    2 ^ S.width ≤ Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  have hσ2 : σ * σ = 1 := S.ρ_mul_self hxM (by rw [pow_two]; exact hxx)
  have hPC := S.card_clPre_fixSpace_le hxM
  have hPcard : Nat.card (S.clPre (fixSpace σ)) = 2 * 2 ^ finrank (ZMod 2) (fixSpace σ) := by
    rw [S.card_clPre, S.card_submodule]
  have hdim : S.width ≤ finrank (ZMod 2) (fixSpace σ) := by
    have h1 := finrank_commSpace_add_finrank_fixSpace σ
    have h3 := Submodule.finrank_mono (commSpace_le_fixSpace hσ2)
    rw [S.finrank_Qt_eq_two_mul_width] at h1
    omega
  have h1 : 2 ^ S.width ≤ 2 ^ finrank (ZMod 2) (fixSpace σ) :=
    Nat.pow_le_pow_right (by norm_num) hdim
  rw [← hσ] at hPC
  omega

end Setting

namespace S14

@[expose] def AschbacherTIInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
    IsSimpleGroup S.zGen → centralizer (S.zGen : Set G) = ⊥ →
    ∀ g : G, g ∉ S.M → g * S.z * g⁻¹ ∈ S.M →
      (∀ a ∈ S.tiR g, ∀ b ∈ S.tiR g, a * b = b * a) ∧
      (S.tiS g = S.QG ∨ ((S.tiS g).relIndex S.QG = 2 ∧
        closure {x | x ∈ S.tiS g ∧ x * x = 1} = S.tiR g)) ∧
      ∀ r ∈ S.tiR g, r * r = 1 → ∀ s ∈ S.tiS g, r * s = s * r

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem card_le_four_of_abelian {R : Subgroup G} (hRQ : R ≤ S.QG)
    (hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hinv : ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = S.z) :
    Nat.card R ≤ 4 := by
  have hsq : ∀ r ∈ R, r * r = 1 ∨ r * r = S.z := fun r hr => by
    have := S.sq_eq_one_or_z (hRQ hr)
    rwa [pow_two] at this
  have key : ∃ a : G, (R : Set G) ⊆ {1, S.z, a, a * S.z} := by
    by_cases h : ∃ a ∈ R, a * a = S.z
    · obtain ⟨a, haR, ha2⟩ := h
      have hainv : a⁻¹ = a * S.z :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ha2, S.z_mul_z])
      refine ⟨a, fun b hbR => ?_⟩
      rcases hsq b hbR with hb | hb
      · rcases hinv b hbR hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have h2 : a * b * (a * b) = 1 := by
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab b hbR a haR]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb, S.z_mul_z]
        rcases hinv _ (R.mul_mem haR hbR) h2 with h1 | h1
        · right; right; right
          calc b = a⁻¹ * (a * b) := by group
            _ = a * S.z := by rw [h1, mul_one, hainv]
        · right; right; left
          calc b = a⁻¹ * (a * b) := by group
            _ = a * S.z * S.z := by rw [h1, hainv]
            _ = a := by rw [mul_assoc, S.z_mul_z, mul_one]
    · push Not at h
      refine ⟨1, fun b hbR => ?_⟩
      rcases hsq b hbR with hb | hb
      · rcases hinv b hbR hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact absurd hb (h b hbR)
  obtain ⟨a, ha⟩ := key
  have h1 := Set.ncard_le_ncard ha (Set.toFinite _)
  have h2 : ({1, S.z, a, a * S.z} : Set G).ncard ≤ 4 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
    rw [Set.ncard_singleton]
  have hcard : Nat.card R = (R : Set G).ncard := Nat.card_coe_set_eq (R : Set G)
  omega

theorem fourNine (h75 : S14.AschbacherTIInput) (hn : 3 ≤ S.width)
    (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) : S.M = ⊤ := by
  by_contra hMtop
  have hZ : S.z ∉ center G := fun h => hMtop (eq_top_iff.mpr fun g _ =>
    S.mem_M_iff.mpr (mem_center_iff.mp h g))
  have hCt : ∀ t ∈ S.QG, t ≠ 1 → centralizer ({t} : Set G) ≤ S.M := by
    intro t ht ht1 c hc
    apply hTI c
    intro h0
    have htc : t ∈ S.QG ⊓ S.Qa c :=
      mem_inf.mpr ⟨ht, S.mem_Qa_of_commute ht (mem_centralizer_singleton_iff.mp hc)⟩
    rw [h0, mem_bot] at htc
    exact ht1 htc
  have hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z := by
    intro g hg
    have hgM : g ∈ S.M := by
      apply hTI g
      intro h0
      have h1 : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa g :=
        mem_inf.mpr ⟨hg, by rw [S.Qa_eq_map]; exact ⟨S.z, S.z_mem_QG, rfl⟩⟩
      rw [h0, mem_bot] at h1
      apply S.z_ne_one
      calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [S.mem_M_iff.mp hgM]
    group
  have hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t := fun t ht ht2 =>
    S.zInOTwo_of_centralizer_le ht (hCt t ht fun h => by
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by norm_num))
  obtain ⟨hsimp, hC⟩ := S.isSimpleGroup_zGen_of_weaklyClosed (by omega) hO hZ hW
  obtain ⟨g, hgM, hgz⟩ : ∃ g : G, g ∉ S.M ∧ g * S.z * g⁻¹ ∈ S.M := by
    by_contra! hiso
    obtain ⟨N, hNn, hNodd, hN⟩ := S10.exists_odd_normal_of_isolated S.z S.z_ne_one S.z_mul_z
      (fun g hg => by
        by_cases hgM : g ∈ S.M
        · rw [S.mem_M_iff.mp hgM]
          group
        · exact absurd (S.mem_M_iff.mpr hg) (hiso g hgM))
    have hN1 := S.eq_bot_of_normal_odd (by omega) hO hNn hNodd
    apply hZ
    rw [mem_center_iff]
    intro g
    have h := hN g
    rw [hN1, mem_bot, mul_inv_eq_one] at h
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [h]
  obtain ⟨hRab, hScase, hRS⟩ := h75 G S hn hTI hW hsimp hC g hgM hgz
  have hxx : g * S.z * g⁻¹ * (g * S.z * g⁻¹) = 1 := by
    rw [show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, S.z_mul_z]
    group
  have hR8 : 2 ^ S.width ≤ Nat.card (S.tiR g) := S.two_pow_width_le_card_centralizer hgz hxx
  have hRQ : S.tiR g ≤ S.QG := inf_le_left
  have hR4 : Nat.card (S.tiR g) ≤ 4 := by
    rcases hScase with hS | ⟨hrel, hgen⟩
    · refine S.card_le_four_of_abelian hRQ hRab fun r hr hrr => ?_
      refine S.eq_one_or_z_of_commute (hRQ hr) fun y hy => ?_
      exact hRS r hr hrr y (hS ▸ hy)
    ·
      have hsq : ∀ r ∈ S.tiR g, r * r = 1 := by
        intro r hr
        rw [← hgen] at hr
        induction hr using closure_induction with
        | mem x hx => exact hx.2
        | one => exact mul_one 1
        | mul x y hx hy ihx ihy =>
          rw [hgen] at hx hy
          rw [show x * y * (x * y) = x * (y * x) * y by group, ← hRab x hx y hy,
            show x * (x * y) * y = (x * x) * (y * y) by group, ihx, ihy, mul_one]
        | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]
      have hcent : ∀ r ∈ S.tiR g, ∀ s ∈ S.tiS g, r * s = s * r := fun r hr =>
        hRS r hr (hsq r hr)
      by_cases hr₀ : ∃ r₀ ∈ S.tiR g, r₀ ≠ 1 ∧ r₀ ≠ S.z
      · obtain ⟨r₀, hr₀R, hr₀1, hr₀z⟩ := hr₀
        have hr₀Q : r₀ ∈ S.QG := hRQ hr₀R
        have hSQ : S.tiS g ≤ S.QG := inf_le_left
        have hSC : S.tiS g ≤ S.QG ⊓ centralizer ({r₀} : Set G) := fun s hs => mem_inf.mpr
          ⟨hSQ hs, mem_centralizer_singleton_iff.mpr (hcent r₀ hr₀R s hs).symm⟩
        have hrelC := S.relIndex_centralizer_eq_two hr₀Q hr₀1 hr₀z
        have hcardS : Nat.card S.QG = 2 * Nat.card (S.tiS g) := by
          have := Subgroup.card_mul_index ((S.tiS g).subgroupOf S.QG)
          rw [Nat.card_congr (subgroupOfEquivOfLe hSQ).toEquiv] at this
          change _ * (S.tiS g).relIndex S.QG = _ at this
          rw [hrel] at this
          omega
        have hcardC : Nat.card S.QG =
            2 * Nat.card ↥(S.QG ⊓ centralizer ({r₀} : Set G)) := by
          have := Subgroup.card_mul_index
            ((S.QG ⊓ centralizer ({r₀} : Set G)).subgroupOf S.QG)
          rw [Nat.card_congr (subgroupOfEquivOfLe
            (inf_le_left : S.QG ⊓ centralizer ({r₀} : Set G) ≤ S.QG)).toEquiv] at this
          change _ * (S.QG ⊓ centralizer ({r₀} : Set G)).relIndex S.QG = _ at this
          rw [hrelC] at this
          omega
        have hSeq : S.tiS g = S.QG ⊓ centralizer ({r₀} : Set G) :=
          Subgroup.eq_of_le_of_card_ge hSC (by omega)
        have hsub : (S.tiR g : Set G) ⊆ {1, S.z, r₀, r₀ * S.z} := by
          intro r hr
          have hrC : r ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({r₀} : Set G) :
              Subgroup G) : Set G) := by
            refine mem_inf.mpr ⟨hRQ hr, mem_centralizer_iff.mpr fun c hc => ?_⟩
            rw [← hSeq] at hc
            exact (hcent r hr c hc).symm
          rcases (S.mem_centralizer_centralizer_iff hr₀Q).mp hrC with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 : ({1, S.z, r₀, r₀ * S.z} : Set G).ncard ≤ 4 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
          refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1)
            1).trans ?_
          rw [Set.ncard_singleton]
        have hcard : Nat.card (S.tiR g) = (S.tiR g : Set G).ncard :=
          Nat.card_coe_set_eq (S.tiR g : Set G)
        omega
      · push Not at hr₀
        refine S.card_le_four_of_abelian hRQ hRab fun r hr _ => ?_
        by_cases hr1 : r = 1
        · exact Or.inl hr1
        · exact Or.inr (hr₀ r hr hr1)
  have h8 : 2 ^ 3 ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem exists_inf_Qa_ne_bot (h75 : S14.AschbacherTIInput) (hn : 3 ≤ S.width)
    (hM : S.M ≠ ⊤) : ∃ g : G, g ∉ S.M ∧ S.QG ⊓ S.Qa g ≠ ⊥ := by
  by_contra! h
  exact hM (S.fourNine h75 hn fun g hg => by
    by_contra hgM
    exact hg (h g hgM))

end Setting

end CFSG.LargeExtraspecial
