module

public import CFSG.CGT.HaradaParrott80.Setup

public section

namespace CFSG.CGT.HaradaParrott80

open CFSG CFSG.QuasithinUnique CFSG.CGT.Harada80 QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial.OrthoF2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)

omit [Finite G] in
theorem conj_mem_centralizer {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (H : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := Subgroup.inv_mem _ hg
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hg' y).mp hy
  rw [inv_inv] at hy'
  have h := hc _ hy'
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * y := by group

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer hg, fun hc => ?_⟩
  have h := conj_mem_centralizer (Subgroup.inv_mem _ hg) hc
  rwa [inv_inv, show g⁻¹ * (g * c * g⁻¹) * g = c by group] at h

theorem exists_mem_normalizer_of_lt {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hP : IsPGroup p P) (hHP : H < P) :
    ∃ x ∈ P, x ∉ H ∧ x ∈ Subgroup.normalizer (H : Set G) := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hlt : H.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hHP.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ H.subgroupOf P := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨⟨x, hxP⟩, hxN, hxH⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨x, hxP, fun hx => hxH (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN ⟨h, hHP.le hh⟩).mp
      (Subgroup.mem_subgroupOf.mpr hh)
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hh
    have hhP : h ∈ P := by
      have h2 := P.mul_mem (P.mul_mem (P.inv_mem hxP) (hHP.le hh)) hxP
      rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at h2
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hxN ⟨h, hhP⟩).mpr (Subgroup.mem_subgroupOf.mpr hh))

include S in
theorem isPGroup_blockU : IsPGroup 2 (blockU J) := fun u =>
  ⟨1, Subtype.ext (by rw [SubgroupClass.coe_pow, pow_one]; exact S.elemU.2 u u.2)⟩

include S in
theorem mul_self_eq_one {u : G} (hu : u ∈ blockU J) : u * u = 1 := by
  rw [← pow_two]
  exact S.elemU.2 u hu

theorem vec_mem_span_iff (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (u : ↥(blockU J)) :
    S.vec u ∈ (ZMod 2) ∙ S.vec a ↔ (u : G) = 1 ∨ (u : G) = a := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · left
      rw [zero_smul] at hc
      exact congrArg Subtype.val ((S.vec_eq_zero_iff hZ).mp hc.symm)
    · right
      rw [one_smul] at hc
      exact congrArg Subtype.val (S.vec_injective hZ hc.symm)
  · rintro (h | h)
    · rw [show u = 1 from Subtype.ext h, S.vec_one]
      exact Submodule.zero_mem _
    · rw [show u = a from Subtype.ext h]
      exact Submodule.mem_span_singleton_self _

theorem vec_commutator (hZ : blockZ J = ⊥) (x : ↥M) (u : ↥(blockU J))
    (h : (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ ∈ blockU J) :
    S.vec ⟨_, h⟩ = S.lin hZ x (S.vec u) - S.vec u := by
  rw [show (⟨_, h⟩ : ↥(blockU J)) =
      ⟨(x : G) * u * (x : G)⁻¹, Setting.conj_mem_blockU S x.2 u.2⟩ * u⁻¹ from rfl,
    S.vec_mul, vec_inv, ← S.lin_vec hZ x u, sub_eq_add_neg]

include S in
theorem commutator_mem_blockU_of_mem {x u : G} (hx : x ∈ M) (hu : u ∈ blockU J) :
    x * u * x⁻¹ * u⁻¹ ∈ blockU J :=
  (blockU J).mul_mem (Setting.conj_mem_blockU S hx hu) ((blockU J).inv_mem hu)

theorem mem_blockU_of_commutator_mem (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha : quadQ m (S.vec a) = 0)
    {x : G} (hx : x ∈ M)
    (h : ∀ u ∈ blockU J, x * u * x⁻¹ * u⁻¹ = 1 ∨ x * u * x⁻¹ * u⁻¹ = a) : x ∈ blockU J := by
  refine (lin_eq_one_iff_mem S hH1 hZ hC ⟨x, hx⟩).mp ?_
  refine eq_one_of_forall_sub_mem_span (nondegenerate_quadQ m) ha
    (S.lin_mem_orthogonalGroup hZ _) fun z => ?_
  obtain ⟨u, rfl⟩ := S.vec_surjective z
  rw [← vec_commutator S hZ ⟨x, hx⟩ u (commutator_mem_blockU_of_mem S hx u.2)]
  exact (vec_mem_span_iff S hZ _).mpr (h u u.2)

theorem exists_mem_rootSub_lin_eq (hZ : blockZ J = ⊥) {a : ↥(blockU J)}
    {g : Vec m ≃ₗ[ZMod 2] Vec m} (hg : g ∈ rootGroup (quadQ m) (S.vec a)) :
    ∃ x : ↥M, (x : G) ∈ rootSub S hZ a ∧ S.lin hZ x = g := by
  obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ
    (rootGroup_le_elementaryGroup (quadQ m) (S.vec a) hg)
  exact ⟨Subgroup.inclusion S.le ℓ, (mem_rootSub S).mpr ⟨_, hℓ ▸ hg⟩, hℓ⟩

theorem eq_one_or_eq_of_commute_rootSub (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {u : G} (hu : u ∈ blockU J)
    (hc : ∀ r ∈ rootSub S hZ a, r * u = u * r) : u = 1 ∨ u = a := by
  refine (vec_mem_span_iff S hZ ⟨u, hu⟩).mp ?_
  by_contra hns
  obtain ⟨g, hg, hgne⟩ := exists_mem_rootGroup_apply_ne (nondegenerate_quadQ m) ha
    (vec_ne_zero S hZ ha1) (le_trans (by norm_num) (five_le_finrank S)) hns
  obtain ⟨x, hxR, rfl⟩ := exists_mem_rootSub_lin_eq S hZ hg
  apply hgne
  refine (S.lin_vec_eq_iff hZ x ⟨u, hu⟩).mpr ?_
  rw [hc _ hxR, mul_inv_cancel_right]

theorem eq_one_or_eq_of_mem_center_rootSub (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {z : G} (hz : z ∈ rootSub S hZ a)
    (hc : ∀ r ∈ rootSub S hZ a, z * r = r * z) : z = 1 ∨ z = a := by
  have hzA : z ∈ blockU J := S.mem_blockU_of_centralizer hH1 hZ hC (rootSub_le S hZ a hz)
    fun v hv => by rw [hc v (blockU_le_rootSub S hZ a hv), mul_inv_cancel_right]
  exact eq_one_or_eq_of_commute_rootSub S hZ ha1 ha hzA fun r hr => (hc r hr).symm

theorem commutator_eq_of_mem_perpSub (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {y : G} (hy : y ∈ perpSub S a) {r : G}
    (hr : r ∈ rootSub S hZ a) : r * y * r⁻¹ * y⁻¹ = 1 ∨ r * y * r⁻¹ * y⁻¹ = a := by
  obtain ⟨hyA, hy0⟩ := hy
  obtain ⟨hrM, hrR⟩ := (mem_rootSub S).mp hr
  obtain ⟨-, -, hperp⟩ :=
    (mem_rootGroup_iff (nondegenerate_quadQ m) ha (vec_ne_zero S hZ ha1)).mp hrR
  obtain ⟨c, hc⟩ := hperp _ hy0
  have hmem := commutator_mem_blockU_of_mem S hrM hyA
  refine (vec_mem_span_iff S hZ ⟨_, hmem⟩).mp ?_
  rw [vec_commutator S hZ ⟨r, hrM⟩ ⟨y, hyA⟩ hmem, hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_perpSub_of_commutator_eq (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {y : G} (hy : y ∈ rootSub S hZ a)
    (h : ∀ r ∈ rootSub S hZ a, r * y * r⁻¹ * y⁻¹ = 1 ∨ r * y * r⁻¹ * y⁻¹ = a) :
    y ∈ perpSub S a := by
  have hyM := rootSub_le S hZ a hy
  have ha2 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_left (mul_self_eq_one S a.2)
  have hinv : ∀ u : G, u = 1 ∨ u = a → u⁻¹ = 1 ∨ u⁻¹ = a := by
    rintro u (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr ha2
  have hyA : y ∈ blockU J := by
    refine mem_blockU_of_commutator_mem S hH1 hZ hC ha hyM fun u hu => ?_
    have h1 := hinv _ (h u (blockU_le_rootSub S hZ a hu))
    rwa [show (u * y * u⁻¹ * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ by group] at h1
  refine (mem_perpSub_iff S ⟨y, hyA⟩).mpr ?_
  by_contra hne
  obtain ⟨g, hg, hg1⟩ := exists_mem_rootGroup_ne_one (nondegenerate_quadQ m) ha
    (vec_ne_zero S hZ ha1) (le_trans (by norm_num) (five_le_finrank S))
  obtain ⟨x, hxR, rfl⟩ := exists_mem_rootSub_lin_eq S hZ hg
  apply sub_not_mem_span_of_mem_rootGroup (nondegenerate_quadQ m) ha hg hg1 hne
  have hmem := commutator_mem_blockU_of_mem S x.2 hyA
  rw [← vec_commutator S hZ x ⟨y, hyA⟩ hmem]
  exact (vec_mem_span_iff S hZ _).mpr (h x hxR)

theorem normalizer_rootSub_le (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) :
    Subgroup.normalizer (rootSub S hZ a : Set G) ≤ Subgroup.normalizer (perpSub S a : Set G) := by
  set R := rootSub S hZ a
  have hconjR : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ r ∈ R, g * r * g⁻¹ ∈ R :=
    fun g hg r hr => (Subgroup.mem_normalizer_iff.mp hg r).mp hr
  have haR : (a : G) ∈ R := blockU_le_rootSub S hZ a a.2
  have hfix : ∀ g ∈ Subgroup.normalizer (R : Set G), g * a * g⁻¹ = a := by
    intro g hg
    have hcen : ∀ r ∈ R, g * a * g⁻¹ * r = r * (g * a * g⁻¹) := by
      intro r hr
      have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := hconjR _ (Subgroup.inv_mem _ hg) r hr
      rw [inv_inv] at hr'
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
        (rootSub_le_centralizer S hZ a hr')
      calc g * a * g⁻¹ * r = g * (a * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * a) * g⁻¹ := by rw [hcomm]
        _ = r * (g * a * g⁻¹) := by group
    rcases eq_one_or_eq_of_mem_center_rootSub S hH1 hZ hC ha1 ha (hconjR g hg _ haR) hcen with
      h | h
    · exact absurd (Subtype.ext (by simpa using h)) ha1
    · exact h
  have hmain : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ y ∈ perpSub S a,
      g * y * g⁻¹ ∈ perpSub S a := by
    intro g hg y hy
    have hyR : y ∈ R := blockU_le_rootSub S hZ a (perpSub_le_blockU S a hy)
    refine mem_perpSub_of_commutator_eq S hH1 hZ hC ha1 ha (hconjR g hg y hyR) fun r hr => ?_
    have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := hconjR _ (Subgroup.inv_mem _ hg) r hr
    rw [inv_inv] at hr'
    have hconj : r * (g * y * g⁻¹) * r⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * ((g⁻¹ * r * g) * y * (g⁻¹ * r * g)⁻¹ * y⁻¹) * g⁻¹ := by group
    rw [hconj]
    rcases commutator_eq_of_mem_perpSub S hZ ha1 ha hy hr' with h | h
    · left
      rw [h, mul_one, mul_inv_cancel]
    · right
      rw [h]
      exact hfix g hg
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hmain g hg y, fun hy => ?_⟩
  have h := hmain g⁻¹ (Subgroup.inv_mem _ hg) _ hy
  rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h

theorem eq_blockU_of_le_centralizer (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha : quadQ m (S.vec a) = 0)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hAX : blockU J ≤ X)
    (hXC : X ≤ Subgroup.centralizer (perpSub S a : Set G)) : X = blockU J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨x, hxX, hxA, hxN⟩ := exists_mem_normalizer_of_lt hX (lt_of_le_of_ne hAX (Ne.symm hne))
  rw [Setting.normalizer_blockU_eq S] at hxN
  refine hxA (mem_blockU_of_centralizer_perpSub S hH1 hZ hC ha hxN fun u hu => ?_)
  rw [(Subgroup.mem_centralizer_iff.mp (hXC hxX) u hu).symm, mul_inv_cancel_right]

theorem normalizer_perpSub_le (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) :
    Subgroup.normalizer (perpSub S a : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 := isPGroup_blockU S
  have hA₁2 : IsPGroup 2 (perpSub S a) := hA2.to_le (perpSub_le_blockU S a)
  have hA₁1 : perpSub S a ≠ ⊥ := fun h => ha1 (Subtype.ext (by
    have h1 := mem_perpSub_self S ha
    rw [h, Subgroup.mem_bot] at h1
    exact h1))
  obtain ⟨C', hC'⟩ : ∃ C' : Subgroup G, C' = Subgroup.centralizer (perpSub S a : Set G) :=
    ⟨_, rfl⟩
  have hchar : IsCharacteristicP 2 ↥C' :=
    hC' ▸ CFSG.CGT.PushingUpLit.T2K.isCharacteristicP_centralizer S.charTwo hA₁2 hA₁1
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = CFSG.Open.pCoreOf 2 C' := ⟨_, rfl⟩
  have hP2 : IsPGroup 2 P := hP ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C'
  have hPC : P ≤ C' := hP ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 C'
  have hAC : blockU J ≤ C' := fun u hu => hC' ▸ Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Setting.blockU_comm S (perpSub_le_blockU S a hy) hu
  have hPA : P ≤ blockU J := by
    have hsup := eq_blockU_of_le_centralizer S hH1 hZ hC ha
      (IsPGroup.to_sup_of_normal_left' hP2 hA2
        (hAC.trans (hP ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C'))) le_sup_right
      (hC' ▸ sup_le hPC hAC)
    rw [← hsup]
    exact le_sup_left
  have hAP : blockU J ≤ P := by
    intro u hu
    rw [hP]
    refine ⟨⟨u, hAC hu⟩, hchar (Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_), rfl⟩
    exact Setting.blockU_comm S (hPA (hP ▸ ⟨y, hy, rfl⟩)) hu
  have hPeq : CFSG.Open.pCoreOf 2 C' = blockU J := hP ▸ le_antisymm hPA hAP
  intro g hg
  have hgP := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C'
    (hC' ▸ normalizer_le_normalizer_centralizer _ hg)
  rw [hPeq, Setting.normalizer_blockU_eq S] at hgP
  exact hgP

end CFSG.CGT.HaradaParrott80
