module

public import CFSG.GH74.Uniqueness.Section172Frat
public import CFSG.GH74.Uniqueness.Section12Center
public import CFSG.GH74.Uniqueness.Section172Omega

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem Sec173.mem_normalizer_of_conj_mem {H : Subgroup X} {g : X}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set X) := by
  let φ : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hφ : Function.Injective φ := fun x y hxy => by
    have h1 : g * (x : X) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hφs := Finite.surjective_of_injective hφ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := hφs ⟨g * y * g⁻¹, hy⟩
  have hxy : (x : X) = y := by
    have h1 : g * (x : X) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hx
    exact mul_left_cancel (mul_right_cancel h1)
  exact hxy ▸ x.2

omit [Finite X] in
theorem Sec173.mem_or_mul_mem_of_mem_sup {N : Subgroup X} {t : X} (ht2 : t * t = 1)
    (htN : t ∈ normalizer (N : Set X)) {x : X} (hx : x ∈ N ⊔ zpowers t) : x ∈ N ∨ x * t ∈ N := by
  have hle : zpowers t ≤ normalizer (N : Set X) := Subgroup.zpowers_le.mpr htN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N (zpowers t) hle] at hx
  obtain ⟨n, hn, k, hk, hnk⟩ := hx
  have hx' : x = n * k := hnk.symm
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have ht2' : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
  rw [hx']
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' j
  · left
    rw [hm, zpow_mul, ht2', one_zpow, mul_one]
    exact hn
  · right
    rw [hm, zpow_add_one, zpow_mul, ht2', one_zpow, one_mul, mul_assoc, ht2, mul_one]
    exact hn

omit [Finite X] in
theorem Sec173.centralizer_conj (g t : X) :
    centralizer ({g⁻¹ * t * g} : Set X) = conjugate (centralizer ({t} : Set X)) g := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g * x) * g⁻¹ := by rw [h]
      _ = t * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * t * g) = g⁻¹ * (g * x * g⁻¹ * t) * g := by group
      _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * t * g * x := by group

theorem BenderSub.odd_card_center {F : Subgroup X} {n i e : ℕ} (hB : BenderSub Z M F n i e) :
    Odd (Nat.card (center ↥F)) := by
  have h1 := odd_card_pPrimeCoreIn F
  rwa [hB.core, card_map_of_injective F.subtype_injective] at h1

theorem ZDSetup.benderType_of_benderSub
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) (hi : i = 1 ∨ i = 2) : Bender.BenderType ↥F n i e := by
  have hgen : closure {x : ↥F | x * x = 1} = ⊤ := by
    have hle : F ≤ (closure {x : ↥F | x * x = 1}).map F.subtype := by
      have h1 : zHull Z F ≤ (closure {x : ↥F | x * x = 1}).map F.subtype := by
        refine (closure_le _).mpr fun y hy => ?_
        refine ⟨⟨y, hy.2⟩, subset_closure ?_, rfl⟩
        exact Subtype.ext (S.invariant.mul_self_eq_one hy.1)
      rwa [hB.zhull] at h1
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  exact benderType_of_center_eq_bot hB.bender
    (center_eq_bot_of_benderType hi hgen hB.odd_card_center hB.bender)

omit [Finite X] in
theorem Sec173.relIndex_eq_card_of_inv {A : Subgroup X} {s : X} (hA : Odd (Nat.card A))
    (hinv : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹) :
    (centralizer ({s} : Set X)).relIndex A = Nat.card A := by
  have hbot : centralizer ({s} : Set X) ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haC, haA⟩ := Subgroup.mem_inf.mp ha
    rw [Subgroup.mem_bot]
    have h1 : s * a * s⁻¹ = a := by
      rw [Subgroup.mem_centralizer_singleton_iff] at haC
      rw [← haC]
      group
    have h2 : a * a = 1 := by
      have := hinv a haA
      rw [h1] at this
      calc a * a = a * a⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel a
    have hodd : Odd (orderOf a) := Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A haA)
    exact Sec172.eq_one_of_sq h2 hodd
  have := Subgroup.relIndex_mul_card (centralizer ({s} : Set X)) A
  rwa [hbot, Subgroup.card_bot, mul_one] at this

omit [Finite X] in
theorem Sec173.subgroupOf_facts {F A : Subgroup X} (hAF : A ≤ F) {s : X} (hsF : s ∈ F)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A) (hA1 : A ≠ ⊥) :
    Nat.card ↥(A.subgroupOf F) = Nat.card A ∧ A.subgroupOf F ≠ ⊥ ∧
      (⟨s, hsF⟩ : ↥F) * ⟨s, hsF⟩ = 1 ∧ (⟨s, hsF⟩ : ↥F) ≠ 1 ∧
      (⟨s, hsF⟩ : ↥F) ∈ normalizer ((A.subgroupOf F : Subgroup ↥F) : Set ↥F) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  refine ⟨Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv, ?_, Subtype.ext hs2,
    fun h => hs1 (congrArg Subtype.val h), ?_⟩
  · intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAF ha⟩ : ↥F) ∈ A.subgroupOf F := Subgroup.mem_subgroupOf.mpr ha
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · exact hsA _
    · intro hy
      have := hsA _ hy
      rwa [hsi, show s * (s * (y : X) * s) * s = (s * s) * y * (s * s) by group, hs2, one_mul,
        mul_one] at this

theorem ZDSetup.exists_pair_B0 (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M)
    (h172 : Lemma172Stmt Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    ∃ (A : Subgroup X) (s : X), A ≤ cenHull Z c.u ∧ Odd (Nat.card A) ∧ s ∈ cenHull Z c.u ∧
      s * s = 1 ∧ s ≠ 1 ∧ (∀ a ∈ A, s * a * s⁻¹ ∈ A) ∧
      (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex
          (c.D ⊓ centralizer ({c.t * c.u} : Set X)) =
        (centralizer ({s} : Set X)).relIndex A ∧
      (centralizer ({s} : Set X)).relIndex A ≡ 1 [MOD 2 ^ n] ∧
      (centralizer ({s} : Set X)).relIndex A ≠ 1 ∧
      (∀ y ∈ cenHull Z c.u, ¬ A ≤ conjugate M y) ∧
      (∀ x ∈ cenHull Z c.u, (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A ∨ x * s ∈ A) := by
  obtain ⟨-, h172b, h172c, h172d, h172e, h172f⟩ := h172 c n i e hB
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.isConj_u_tu h166 c hB)
  set D₀ : Subgroup X := c.D ⊓ cenHull Z (c.t * c.u) with hD₀
  set W : Subgroup X := cenHull Z (c.t * c.u) with hW
  have ht2 : c.t * c.t = 1 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have htD : c.t ∈ normalizer (c.D : Set X) := mem_normalizer_inf_conjugate ht2
  have htW : c.t ∈ normalizer (W : Set X) := Sec172.t_mem_normalizer_cenHull S c
  have htD₀ : ∀ d ∈ D₀, c.t * d * c.t⁻¹ ∈ D₀ := by
    intro d hd
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htD d).mp hd.1,
      (Subgroup.mem_normalizer_iff.mp htW d).mp hd.2⟩
  have hBW : ∀ x, x ∈ cenHull Z c.u → g * x * g⁻¹ ∈ W := by
    intro x hx
    have := Sec172.mem_cenHull_conj S.invariant g hx
    rwa [hg] at this
  have hWB : ∀ x, x ∈ W → g⁻¹ * x * g ∈ cenHull Z c.u := by
    intro x hx
    have := Sec172.mem_cenHull_conj S.invariant g⁻¹ (v := c.t * c.u) hx
    rwa [← hg, inv_inv, show g⁻¹ * (g * c.u * g⁻¹) * g = c.u by group] at this
  set A : Subgroup X := conjugate D₀ g with hA
  set s : X := g⁻¹ * c.t * g with hs
  have hmemA : ∀ x, x ∈ A ↔ g * x * g⁻¹ ∈ D₀ := fun x => mem_conjugate_iff
  have hcval := S.lemma172g c n i e hB
  rw [Subgroup.inf_relIndex_left] at hcval
  have hcA : (centralizer ({s} : Set X)).relIndex A =
      (centralizer ({c.t} : Set X)).relIndex D₀ := by
    rw [hs, Sec173.centralizer_conj, hA]
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective
  refine ⟨A, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    have h1 := hWB _ ((hmemA x).mp hx).2
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  ·
    rw [hA, card_conjugate]
    exact h172d
  ·
    exact hWB _ (Sec172.t_mem_cenHull c)
  ·
    calc g⁻¹ * c.t * g * (g⁻¹ * c.t * g) = g⁻¹ * (c.t * c.t) * g := by group
      _ = 1 := by rw [ht2]; group
  ·
    intro h1
    have : c.t = 1 := by
      calc c.t = g * s * g⁻¹ := by rw [hs]; group
        _ = 1 := by rw [h1]; group
    rw [this] at ht2
    have hZ := S.invariant.1 _ c.ht
    rw [this, orderOf_one] at hZ
    exact absurd hZ (by norm_num)
  ·
    intro a ha
    rw [hmemA] at ha ⊢
    have h1 := htD₀ _ ha
    rwa [show c.t * (g * a * g⁻¹) * c.t⁻¹ =
      g * (g⁻¹ * c.t * g * a * (g⁻¹ * c.t * g)⁻¹) * g⁻¹ by group] at h1
  ·
    rw [hcA, hcval]
  · rw [hcA, ← hcval]
    exact h172b
  · rw [hcA, ← hcval]
    exact h172c
  ·
    intro y hy hAy
    have hD₀γ : D₀ ≤ conjugate M (y * g⁻¹) := by
      intro d hd
      have h1 : g⁻¹ * d * g ∈ A := by
        rw [hmemA, show g * (g⁻¹ * d * g) * g⁻¹ = d by group]
        exact hd
      have h2 := mem_conjugate_iff.mp (hAy h1)
      rw [mem_conjugate_iff, show y * g⁻¹ * d * (y * g⁻¹)⁻¹ = y * (g⁻¹ * d * g) * y⁻¹ by group]
      exact h2
    have hγ : conjugate M (y * g⁻¹) ∈ omegaFix M (D₀ : Set X) :=
      S.prodDisc.mem_omegaFix_iff.mpr ⟨⟨y * g⁻¹, rfl⟩, hD₀γ⟩
    rw [h172e] at hγ
    have hyu : y * c.u * y⁻¹ = c.u := by
      have hyC : y ∈ centralizer ({c.u} : Set X) := Cor713.zHull_le _ hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC
      rw [hyC]
      group
    have htuγ : c.t * c.u ∈ conjugate M (y * g⁻¹) := by
      rw [mem_conjugate_iff, ← hg,
        show y * g⁻¹ * (g * c.u * g⁻¹) * (y * g⁻¹)⁻¹ = y * c.u * y⁻¹ by group, hyu]
      exact (Subgroup.mem_inf.mp c.hu).1
    have huM : c.u ∈ M := (Subgroup.mem_inf.mp c.hu).1
    rcases hγ with hγ | hγ
    · rw [hγ] at htuγ
      apply c.htM
      have := M.mul_mem htuγ (M.inv_mem huM)
      rwa [mul_inv_cancel_right] at this
    · rw [Set.mem_singleton_iff] at hγ
      rw [hγ, mem_conjugate_iff] at htuγ
      apply c.htM
      have h1 := M.mul_mem (M.inv_mem huM) htuγ
      rw [show c.u⁻¹ * (c.t * (c.t * c.u) * c.t⁻¹) = c.u⁻¹ * (c.t * c.t) * c.u * c.t⁻¹ by group,
        ht2, mul_one, inv_mul_cancel, one_mul] at h1
      have := M.inv_mem h1
      rwa [inv_inv] at this
  ·
    intro x hx hxA
    set x' : X := g * x * g⁻¹ with hx'
    have hx'W : x' ∈ W := hBW x hx
    have hx'N : x' ∈ normalizer (D₀ : Set X) := by
      refine Sec173.mem_normalizer_of_conj_mem fun d hd => ?_
      have h1 : g⁻¹ * d * g ∈ A := by
        rw [hmemA, show g * (g⁻¹ * d * g) * g⁻¹ = d by group]
        exact hd
      have h2 := (hmemA _).mp (hxA _ h1)
      rwa [show g * (x * (g⁻¹ * d * g) * x⁻¹) * g⁻¹ = x' * d * x'⁻¹ by rw [hx']; group] at h2
    have hcomm_ne : ⁅zpowers c.t, D₀⁆ ≠ ⊥ := by
      intro hbot
      apply h172c
      rw [S.lemma172g c n i e hB, Subgroup.inf_relIndex_left, Subgroup.relIndex_eq_one]
      intro d hd
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have h1 := Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_zpowers c.t)) d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr h1
    have hcomm_le : ⁅zpowers c.t, D₀⁆ ≤ D₀ := by
      rw [Subgroup.commutator_le]
      intro a ha d hd
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have htk : c.t ^ k ∈ normalizer (D₀ : Set X) :=
        Subgroup.zpow_mem _ (Sec173.mem_normalizer_of_conj_mem htD₀) k
      rw [commutatorElement_def]
      exact D₀.mul_mem ((Subgroup.mem_normalizer_iff.mp htk d).mp hd) (D₀.inv_mem hd)
    have hf := (h172f D₀ le_rfl hcomm_ne hcomm_le).2 (Subgroup.mem_inf.mpr ⟨hx'N, hx'W⟩)
    rcases Sec173.mem_or_mul_mem_of_mem_sup ht2 (Sec173.mem_normalizer_of_conj_mem htD₀) hf with
      h1 | h1
    · left
      exact (hmemA x).mpr h1
    · right
      rw [hmemA]
      rwa [show g * (x * (g⁻¹ * c.t * g)) * g⁻¹ = x' * c.t by rw [hx']; group]

end CFSG.GH74.Uniqueness
