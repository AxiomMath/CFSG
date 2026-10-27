module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7TransJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Steps
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7KBeta
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecCorr
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Seven

theorem isSimpleGroup_of_lieModel_psp {Y : Type} [Group Y] {n p f : ℕ}
    (h : Blueprint.LieModel Y .PSp n p f) : IsSimpleGroup Y :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem center_eq_bot_of_isPerfect {Y : Type*} [Group Y] [IsSimpleGroup Y] [Group.IsPerfect Y] :
    center Y = ⊥ := by
  rcases (inferInstance : (center Y).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hc : commutator Y = ⊥ := by
      rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro u _
      rw [mem_centralizer_iff]
      intro v _
      exact mem_center_iff.mp (h ▸ mem_top u) v
    have := Group.IsPerfect.commutator_eq_top (G := Y)
    rw [hc] at this
    exact bot_ne_top this

variable {X : Type} [Group X] [Finite X]

theorem IsSylowIn.inf_of_le_normalizer {R M N : Subgroup X} (h : IsSylowIn R M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set X)) : IsSylowIn (R ⊓ N) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRM, R', hR'⟩ := h
  have hn : (N.subgroupOf M).Normal := by
    constructor
    intro n hn m
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hMN m.2) n).mp hn
    simpa using this
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal R' (N := N.subgroupOf M)
  let e : ↥((N.subgroupOf M)) ≃* ↥N := subgroupOfEquivOfLe hNM
  have hsurj : Function.Surjective (e.toMonoidHom : ↥(N.subgroupOf M) →* ↥N) := by
    rw [MulEquiv.coe_toMonoidHom]; exact e.surjective
  refine ⟨inf_le_right, P.mapSurjective hsurj, ?_⟩
  rw [Sylow.coe_mapSurjective, hP, hR']
  ext w
  simp only [mem_map, mem_subgroupOf, mem_inf]
  constructor
  · rintro ⟨v, ⟨hv1, -⟩, rfl⟩
    exact ⟨hv1, (e v).2⟩
  · rintro ⟨hw1, hw2⟩
    refine ⟨e.symm w, ⟨?_, ?_⟩, by simp⟩
    · exact hw1
    · exact (e.symm w).2


omit [Finite X] in
theorem mem_normalizer_inf {A C : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hC : g ∈ normalizer (C : Set X)) : g ∈ normalizer ((A ⊓ C : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro w
  rw [mem_inf, mem_inf]
  exact and_congr (mem_normalizer_iff.mp hA w) (mem_normalizer_iff.mp hC w)

abbrev J0 (h : Hyp52 X) (y : X) : Subgroup X := GSLit.fixedLayer h.J (B0 h y)

abbrev E (h : Hyp52 X) (y : X) : Subgroup X := zpowers h.a ⊔ ⁅h.B, zpowers y⁆

structure Setting (X : Type) [Group X] [Finite X] where
  h : Hyp52 X
  y : X
  hT : h.T = h.B ⊔ zpowers h.a
  hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  hJn : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X)
  hSa : IsSylowIn h.S (centralizer ({h.a} : Set X))
  hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥
  hyP : y ∈ h.P
  hyT : y ∉ h.T
  hy2 : y ^ 2 ∈ h.T
  hyQ : y ∈ normalizer (h.Q : Set X)
  hQ : h.Q ≤ normalizer (B0 h y : Set X)
  h61 : h.Lemma61Shape y
  hS0E : h.S ⊓ normalizer (B0 h y : Set X) ≤ centralizer (E h y : Set X)
  hS0syl : ∃ R : Sylow 2 ↥(normalizer (B0 h y : Set X) ⊓ centralizer (E h y : Set X)),
    (R : Subgroup _) = (h.S ⊓ normalizer (B0 h y : Set X)).subgroupOf
      (normalizer (B0 h y : Set X) ⊓ centralizer (E h y : Set X))
  hKa : conjugate h.K h.a ≠ h.K
  hZK : Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2
  hVL : h.V ≤ Lay h y
  hB0 : B0 h y ≠ ⊥
  p : ℕ
  f : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  hf : 1 ≤ f
  h5 : 5 ≤ p ^ f
  hJLie : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f
  p' : ℕ
  f' : ℕ
  hp' : p'.Prime
  hp2' : p' ≠ 2
  hf' : 1 ≤ f'
  hLLie : Blueprint.LieModel (Lay h y ⧸ pPrimeCore 2 (Lay h y)) .PSp 2 p' f'

namespace Setting

variable (s : Setting X)

theorem a_mul_a : s.h.a * s.h.a = 1 := by
  rw [← pow_two, ← s.h.orderOf_a, pow_orderOf_eq_one]

theorem B0_le_B : B0 s.h s.y ≤ s.h.B := inf_le_left

theorem B0_le_S : B0 s.h s.y ≤ s.h.S := s.B0_le_B.trans s.h.B_le_S

theorem isPGroup_B0 : IsPGroup 2 (B0 s.h s.y) := s.h.isPGroup_B.to_le s.B0_le_B

theorem B0_le_kernel : B0 s.h s.y ≤ coreActionKernel s.h.J :=
  s.B0_le_B.trans (s.h.B_le.trans inf_le_right)

theorem a_mem_centralizer_B0 : s.h.a ∈ centralizer (B0 s.h s.y : Set X) :=
  mem_centralizer_iff.mpr fun _ hb => s.h.comm_a (s.B0_le_S hb)

theorem L_le_centralizer : Lay s.h s.y ≤ centralizer (B0 s.h s.y : Set X) := map_subtype_le _

theorem isPerfect_L : Group.IsPerfect ↥(Lay s.h s.y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.pLayer_perfect 2 (centralizer (B0 s.h s.y : Set X))
  rw [LBalance.Asm.lBalancePLayer_eq_map] at h1
  exact h1

theorem center_Lbar : center (↥(Lay s.h s.y) ⧸ pPrimeCore 2 ↥(Lay s.h s.y)) = ⊥ := by
  have := isSimpleGroup_of_lieModel_psp s.hLLie
  have := s.isPerfect_L
  have : Group.IsPerfect (↥(Lay s.h s.y) ⧸ pPrimeCore 2 ↥(Lay s.h s.y)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact center_eq_bot_of_isPerfect

theorem B0_inf_L : B0 s.h s.y ⊓ Lay s.h s.y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgB, hgL⟩ := mem_inf.mp hg
  have hc : QuotientGroup.mk' (pPrimeCore 2 ↥(Lay s.h s.y)) ⟨g, hgL⟩ ∈
      center (↥(Lay s.h s.y) ⧸ pPrimeCore 2 ↥(Lay s.h s.y)) := by
    rw [mem_center_iff]
    intro u
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (s.L_le_centralizer l.2) g hgB).symm
  rw [s.center_Lbar, mem_bot] at hc
  have hE2 : IsPGroup 2 ((B0 s.h s.y ⊓ Lay s.h s.y).subgroupOf (Lay s.h s.y)) :=
    (s.isPGroup_B0.to_inf_left).comap_subtype
  have h1 := OddQuot.injOn_of_isPGroup hE2 (show (⟨g, hgL⟩ : ↥(Lay s.h s.y)) ∈ _ from
    mem_subgroupOf.mpr hg) (one_mem _) (by rw [map_one]; exact hc)
  exact congrArg Subtype.val h1


theorem exists_beta : ∃ β ∈ s.h.B, β ∈ Lay s.h s.y ∧ β ∉ B0 s.h s.y := by
  obtain ⟨β, hβB, hβK, hβ1⟩ := s.h.exists_mem_B_inf_K s.hKa s.hZK
  have hKV : s.h.K ≤ layerIn (normalizer (s.h.B : Set X)) := s.h.layer_eq_K ▸ le_sup_left
  have hβL : β ∈ Lay s.h s.y := s.hVL (hKV hβK)
  refine ⟨β, hβB, hβL, fun hβ0 => hβ1 ?_⟩
  have := s.B0_inf_L ▸ mem_inf.mpr ⟨hβ0, hβL⟩
  exact mem_bot.mp this

theorem J0_le_J : J0 s.h s.y ≤ s.h.J := (GSLit.fixedLayer_le_inf _ _).trans inf_le_left

theorem J0_le_centralizer_B0 : J0 s.h s.y ≤ centralizer (B0 s.h s.y : Set X) :=
  (GSLit.fixedLayer_le_inf _ _).trans inf_le_right

theorem J0_le_centralizer_a : J0 s.h s.y ≤ centralizer ({s.h.a} : Set X) :=
  s.J0_le_J.trans s.h.J_le

theorem isPComponent_J0 : IsPComponent 2 ((J0 s.h s.y).subgroupOf
    (centralizer ({s.h.a} : Set X) ⊓ centralizer (B0 s.h s.y : Set X))) :=
  Hyp52.isPComponent_secJ0 (h := s.h) (y := s.y)

theorem J0_sup_core : J0 s.h s.y ⊔ (pPrimeCore 2 s.h.J).map s.h.J.subtype = s.h.J ∧
    (pPrimeCore 2 (J0 s.h s.y)).map (J0 s.h s.y).subtype =
      J0 s.h s.y ⊓ (pPrimeCore 2 s.h.J).map s.h.J.subtype :=
  GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J s.h) s.B0_le_kernel s.isPGroup_B0

theorem mem_J0 {z : X} (hzD : z ∈ s.h.D) (hzS : ∀ t ∈ s.h.S, t * z = z * t)
    (hz2 : orderOf z = 2) : z ∈ J0 s.h s.y := by
  show z ∈ GSLit.fixedLayer s.h.J (B0 s.h s.y)
  rw [GSLit.fixedLayer_eq_closure (B5a.isQuasisimple_J s.h) s.B0_le_kernel s.isPGroup_B0]
  exact subset_closure ⟨mem_inf.mpr ⟨s.h.D_le_J hzD,
    mem_centralizer_iff.mpr fun b hb => hzS b (s.B0_le_S hb)⟩, 1, by rw [pow_one]; exact hz2⟩

theorem J0_le_L : J0 s.h s.y ≤ Lay s.h s.y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer (B0 s.h s.y : Set X) with hY
  have haY : s.h.a ∈ Y := s.a_mem_centralizer_B0
  have hza : IsPGroup 2 (zpowers s.h.a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, s.h.orderOf_a, pow_one])
  have hA : IsPGroup 2 ((zpowers s.h.a).subgroupOf Y) := hza.comap_subtype
  have hcA : centralizer (((zpowers s.h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) =
      (centralizer ({s.h.a} : Set X) ⊓ Y).subgroupOf Y := by
    rw [B5a.centralizer_subgroupOf (zpowers_le.mpr haY), centralizer_zpowers_eq,
      inf_subgroupOf_right]
  have hJ0Y : J0 s.h s.y ≤ Y := s.J0_le_centralizer_B0
  have hJA : (J0 s.h s.y).subgroupOf Y ≤
      centralizer (((zpowers s.h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [hcA]
    intro j hj
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨s.J0_le_centralizer_a (mem_subgroupOf.mp hj),
      hJ0Y (mem_subgroupOf.mp hj)⟩)
  have hJc : IsPComponent 2 (((J0 s.h s.y).subgroupOf Y).subgroupOf
      (centralizer (((zpowers s.h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y))) := by
    rw [hcA, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact s.isPComponent_J0
  have hle : (J0 s.h s.y).subgroupOf Y ≤ pLayer ↥Y 2 := by
    have h1 : ((J0 s.h s.y).subgroupOf Y).subgroupOf
        (centralizer (((zpowers s.h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) ≤
        pLayer ↥(centralizer (((zpowers s.h.a).subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) 2 :=
      le_sSup hJc
    have h2 := map_mono (f := (centralizer (((zpowers s.h.a).subgroupOf Y : Subgroup ↥Y) :
      Set ↥Y)).subtype) h1
    rw [map_subgroupOf_eq_of_le hJA] at h2
    exact h2.trans (ClassicalInvolution.l2PrimeBalance ↥Y _ hA)
  intro j hj
  exact ⟨⟨j, hJ0Y hj⟩, hle (mem_subgroupOf.mpr hj), rfl⟩


theorem E_le : E s.h s.y ≤ zpowers s.h.a ⊔ B0 s.h s.y := by
  refine sup_le le_sup_left ?_
  rcases s.h61 with h1 | ⟨b, -, -, -, hbB0, -, hcomm, -⟩
  · rw [h1]
    exact le_sup_left
  · refine hcomm.trans ?_
    rw [closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right hbB0

theorem L_inf_le : Lay s.h s.y ⊓ centralizer ({s.h.a} : Set X) ≤
    normalizer (B0 s.h s.y : Set X) ⊓ centralizer (E s.h s.y : Set X) := by
  intro g hg
  obtain ⟨hgL, hga⟩ := mem_inf.mp hg
  have hgB := s.L_le_centralizer hgL
  refine mem_inf.mpr ⟨centralizer_le_normalizer _ hgB, ?_⟩
  have hle : zpowers s.h.a ⊔ B0 s.h s.y ≤ centralizer ({g} : Set X) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp hga).symm))
      fun w hw => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgB w hw)
  refine Subgroup.centralizer_le s.E_le (mem_centralizer_iff.mpr fun w hw => ?_)
  exact mem_centralizer_singleton_iff.mp (hle hw)

theorem le_normalizer_L_inf : normalizer (B0 s.h s.y : Set X) ⊓ centralizer (E s.h s.y : Set X) ≤
    normalizer ((Lay s.h s.y ⊓ centralizer ({s.h.a} : Set X) : Subgroup X) : Set X) := by
  intro g hg
  obtain ⟨hgN, hgE⟩ := mem_inf.mp hg
  have hgL := normalizer_le_normalizer_layerIn_centralizer _ hgN
  have hga : g ∈ centralizer ({s.h.a} : Set X) := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hgE _ (mem_sup_left (mem_zpowers _))).symm
  exact mem_normalizer_inf hgL (le_normalizer hga)

theorem sylow_S_inf_L : IsSylowIn (s.h.S ⊓ Lay s.h s.y)
    (Lay s.h s.y ⊓ centralizer ({s.h.a} : Set X)) := by
  have h1 : IsSylowIn (s.h.S ⊓ normalizer (B0 s.h s.y : Set X))
      (normalizer (B0 s.h s.y : Set X) ⊓ centralizer (E s.h s.y : Set X)) :=
    ⟨le_inf inf_le_right s.hS0E, s.hS0syl⟩
  have h2 := h1.inf_of_le_normalizer s.L_inf_le s.le_normalizer_L_inf
  have heq : s.h.S ⊓ normalizer (B0 s.h s.y : Set X) ⊓
      (Lay s.h s.y ⊓ centralizer ({s.h.a} : Set X)) = s.h.S ⊓ Lay s.h s.y := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro g hg
      obtain ⟨hgS, hgL⟩ := mem_inf.mp hg
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hgS, centralizer_le_normalizer _
        (s.L_le_centralizer hgL)⟩, mem_inf.mpr ⟨hgL, (mem_inf.mp (s.h.S_le hgS)).1⟩⟩
  rwa [heq] at h2

theorem L_inf_centralizer_eq {c : X} (hc : c ∈ B0 s.h s.y) :
    Lay s.h s.y ⊓ centralizer ({s.h.a * c} : Set X) =
      Lay s.h s.y ⊓ centralizer ({s.h.a} : Set X) := by
  ext g
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun hgL => ?_
  have hgc : c * g = g * c := mem_centralizer_iff.mp (s.L_le_centralizer hgL) c hc
  constructor
  · intro h1
    calc g * s.h.a = g * (s.h.a * c) * c⁻¹ := by group
      _ = s.h.a * c * g * c⁻¹ := by rw [h1]
      _ = s.h.a * (c * g) * c⁻¹ := by group
      _ = s.h.a * (g * c) * c⁻¹ := by rw [hgc]
      _ = s.h.a * g := by group
  · intro h1
    calc g * (s.h.a * c) = g * s.h.a * c := by group
      _ = s.h.a * g * c := by rw [h1]
      _ = s.h.a * (g * c) := by group
      _ = s.h.a * (c * g) := by rw [hgc]
      _ = s.h.a * c * g := by group

theorem L_inf_centralizer_le {c : X} (hc : c ∈ B0 s.h s.y) :
    Lay s.h s.y ⊓ centralizer ({s.h.a * c} : Set X) ≤
      centralizer ({s.h.a} : Set X) ⊓ centralizer (B0 s.h s.y : Set X) := by
  rw [s.L_inf_centralizer_eq hc]
  intro g hg
  exact mem_inf.mpr ⟨(mem_inf.mp hg).2, s.L_le_centralizer (mem_inf.mp hg).1⟩

theorem sylow_D : ∃ R : Sylow 2 ↥s.h.J, (R : Subgroup _) = s.h.D.subgroupOf s.h.J := by
  have h1 : IsSylowIn s.h.S (centralizer ({s.h.a} : Set X) ⊓ normalizer (s.h.J : Set X)) :=
    ⟨s.h.S_le, s.h.S_sylow⟩
  exact (h1.inf_of_le_normalizer (le_inf s.h.J_le le_normalizer) inf_le_right).2

variable {s}

theorem ac_mul_ac {c : X} (hc : c ∈ B0 s.h s.y) (hcc : c * c = 1) :
    s.h.a * c * (s.h.a * c) = 1 := by
  have hca : c * s.h.a = s.h.a * c := s.h.comm_a (s.B0_le_S hc)
  calc s.h.a * c * (s.h.a * c) = s.h.a * (c * s.h.a) * c := by group
    _ = s.h.a * s.h.a * (c * c) := by rw [hca]; group
    _ = 1 := by rw [s.a_mul_a, hcc, one_mul]

theorem ac_ne_one {c : X} (hc : c ∈ B0 s.h s.y) : s.h.a * c ≠ 1 := by
  intro h1
  apply s.h.a_not_mem_B
  rw [show s.h.a = c⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp h1]]
  exact inv_mem (s.B0_le_B hc)

theorem J0_le_centralizer_ac {c : X} (hc : c ∈ B0 s.h s.y) :
    J0 s.h s.y ≤ centralizer ({s.h.a * c} : Set X) := by
  intro j hj
  have hja : j * s.h.a = s.h.a * j := mem_centralizer_singleton_iff.mp (s.J0_le_centralizer_a hj)
  have hjc : c * j = j * c := mem_centralizer_iff.mp (s.J0_le_centralizer_B0 hj) c hc
  rw [mem_centralizer_singleton_iff]
  calc j * (s.h.a * c) = j * s.h.a * c := by group
    _ = s.h.a * (j * c) := by rw [hja]; group
    _ = s.h.a * c * j := by rw [← hjc]; group

theorem commute_z {z : X} (hzS : ∀ t ∈ s.h.S, t * z = z * t) {c : X} (hc : c ∈ B0 s.h s.y) :
    s.h.a * c * z = z * (s.h.a * c) := by
  have h1 := hzS _ s.h.a_mem_S
  have h2 := hzS c (s.B0_le_S hc)
  calc s.h.a * c * z = s.h.a * (c * z) := by group
    _ = s.h.a * z * c := by rw [h2]; group
    _ = z * (s.h.a * c) := by rw [h1]; group

theorem conj_of_cf (hCF : CFSp4Conj) {z : X} (hzD : z ∈ s.h.D)
    (hzS : ∀ t ∈ s.h.S, t * z = z * t) (hz2 : orderOf z = 2) :
    ∀ c ∈ B0 s.h s.y, c * c = 1 → s.h.a * c ∈ Lay s.h s.y →
      ∃ r ∈ Lay s.h s.y, r * r = 1 ∧ r⁻¹ * (s.h.a * c) * r = z := by
  intro c hc hcc hacL
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  exact exists_swap_of_cf hCF s.hp' s.hp2' s.hf' s.hLLie hacL (ac_mul_ac hc hcc) (ac_ne_one hc)
    hzz hz1 (commute_z hzS hc) s.J0_le_L (J0_le_centralizer_ac hc) (s.L_inf_centralizer_le hc)
    s.isPComponent_J0 (s.mem_J0 hzD hzS hz2)

theorem outer_of_cf (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent) {z : X}
    (hzD : z ∈ s.h.D) (hzS : ∀ t ∈ s.h.S, t * z = z * t) (hz2 : orderOf z = 2) :
    ∀ c ∈ B0 s.h s.y, c * c = 1 → s.h.a * c ∈ Lay s.h s.y → ∃ σ ∈ s.h.S, σ ∈ Lay s.h s.y ∧
      ∀ w ∈ s.h.S, (∀ d ∈ s.h.D, w * d = d * w) → w * σ = σ * w → w ∈ s.h.P ∨ z * w ∈ s.h.P := by
  intro c hc hcc hacL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hSL : IsSylowIn (s.h.S ⊓ Lay s.h s.y) (Lay s.h s.y ⊓ centralizer ({s.h.a * c} : Set X)) := by
    rw [s.L_inf_centralizer_eq hc]
    exact s.sylow_S_inf_L
  have hSN : s.h.S ⊓ Lay s.h s.y ≤
      normalizer (s.h.J : Set X) ⊓ normalizer (J0 s.h s.y : Set X) := by
    intro g hg
    obtain ⟨hgS, hgL⟩ := mem_inf.mp hg
    have hgJ := s.h.S_le_normalizer hgS
    exact mem_inf.mpr ⟨hgJ, Hyp52.mem_normalizer_secJ0 (h := s.h) (y := s.y)
      (centralizer_le_normalizer _ (s.L_le_centralizer hgL)) hgJ⟩
  obtain ⟨σ, hσSL, hσJ, hσo⟩ := exists_outer_of_cf hComp hOut s.hp' s.hp2' s.hf' s.hLLie s.hZJ
    hacL (ac_mul_ac hc hcc) (ac_ne_one hc) s.J0_le_J s.J0_le_L (J0_le_centralizer_ac hc)
    (s.L_inf_centralizer_le hc) s.isPComponent_J0 s.J0_sup_core.1 s.J0_sup_core.2 hSL hSN
  obtain ⟨hσS, hσL⟩ := mem_inf.mp hσSL
  refine ⟨σ, hσS, hσL, fun w hwS hwD hwσ => ?_⟩
  have hzS' : z ∈ s.h.S := s.h.D_le_S hzD
  have hzJ : z ∈ normalizer (s.h.J : Set X) := le_normalizer (s.h.D_le_J hzD)
  have hσD : σ ∈ normalizer (s.h.D : Set X) := mem_normalizer_inf (le_normalizer hσS) hσJ
  have h2S : ∀ u ∈ s.h.S, ∃ k : ℕ, u ^ 2 ^ k = 1 := fun u hu => by
    obtain ⟨k, hk⟩ := s.h.isPGroup_S ⟨u, hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hzK : z ∉ coreActionKernel s.h.J := by
    intro hzK
    have : z ∈ s.h.D ⊓ s.h.P := mem_inf.mpr ⟨hzD, mem_inf.mpr ⟨hzS', hzK⟩⟩
    rw [s.h.D_inf_P_eq_bot s.hZJ, mem_bot] at this
    exact hz1 this
  rcases mem_kernel_of_cf hCent s.hp s.hp2 s.hf s.h5 s.hJLie s.sylow_D hσJ
    (s.h.S_le_normalizer hwS) hzJ hσo hσD (h2S w hwS) (h2S z hzS') hwD
    (fun d hd => (hzS d (s.h.D_le_S hd)).symm) hwσ (hzS σ hσS).symm hzK with h1 | h1
  · exact Or.inl (mem_inf.mpr ⟨hwS, h1⟩)
  · right
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    rw [hzi] at h1
    exact mem_inf.mpr ⟨mul_mem hzS' hwS, h1⟩

variable (s)

@[expose] noncomputable def toData (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) : Data X where
  h := s.h
  y := s.y
  z := s.h.exists_involution_D_center.choose
  hT := s.hT
  hC := s.hC
  hJn := s.hJn
  hSa := s.hSa
  hDP := s.h.D_inf_P_eq_bot s.hZJ
  hyP := s.hyP
  hyT := s.hyT
  hy2 := s.hy2
  hyQ := s.hyQ
  hQ := s.hQ
  h61 := s.h61
  hS0E := s.hS0E
  hBL := s.exists_beta
  hB0L := s.B0_inf_L
  hzD := s.h.exists_involution_D_center.choose_spec.1
  hzS := s.h.exists_involution_D_center.choose_spec.2.1
  hz2 := s.h.exists_involution_D_center.choose_spec.2.2
  hconj := conj_of_cf hConj s.h.exists_involution_D_center.choose_spec.1
    s.h.exists_involution_D_center.choose_spec.2.1 s.h.exists_involution_D_center.choose_spec.2.2
  hout := outer_of_cf hComp hOut hCent s.h.exists_involution_D_center.choose_spec.1
    s.h.exists_involution_D_center.choose_spec.2.1 s.h.exists_involution_D_center.choose_spec.2.2

@[simp] theorem toData_h (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) : (s.toData hConj hComp hOut hCent).h = s.h := rfl

@[simp] theorem toData_y (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) : (s.toData hConj hComp hOut hCent).y = s.y := rfl

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB
