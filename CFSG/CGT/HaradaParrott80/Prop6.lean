module

public import CFSG.CGT.HaradaParrott80.Normalizer
public import CFSG.CGT.Harada80.Core

public section

namespace CFSG.CGT.HaradaParrott80

open CFSG CFSG.QuasithinUnique CFSG.CGT.Harada80 QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial.OrthoF2
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)

abbrev qCore {X : Type} [Group X] (a : X) : Subgroup X :=
  CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set X))

omit [Finite G] in
theorem conj_eq_of_mem_centralizer {a x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G)) :
    x * a * x⁻¹ = a :=
  mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hx)

omit [Finite G] in
theorem mem_centralizer_of_conj_eq {a x : G} (h : x * a * x⁻¹ = a) :
    x ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)

theorem isPGroup_qCore (a : G) : IsPGroup 2 (qCore a) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

omit [Finite G] in
theorem qCore_le_centralizer (a : G) : qCore a ≤ Subgroup.centralizer ({a} : Set G) :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 _

omit [Finite G] in
theorem conj_mem_qCore {a x q : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    (hq : q ∈ qCore a) : x * q * x⁻¹ ∈ qCore a :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx) q).mp hq

omit [Finite G] in
theorem centralizer_zpowers_eq (a : G) :
    Subgroup.centralizer (Subgroup.zpowers a : Set G) = Subgroup.centralizer ({a} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hx a (Subgroup.mem_zpowers a)
  · intro hx h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact Commute.zpow_left (hx a (Set.mem_singleton a) : Commute a x) k

include S in
theorem mem_qCore_self (a : ↥(blockU J)) : (a : G) ∈ qCore (a : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.zpowers (a : G) ≤ Subgroup.centralizer ({(a : G)} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hn : Subgroup.centralizer ({(a : G)} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) := by
    rw [← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hn
    ((isPGroup_blockU S).to_le (Subgroup.zpowers_le.mpr a.2)) (Subgroup.mem_zpowers _)

include S in
theorem mem_qCore_of_commute {a : ↥(blockU J)} (ha1 : a ≠ 1) {x : G}
    (hx : x ∈ Subgroup.centralizer ({(a : G)} : Set G))
    (hc : ∀ q ∈ qCore (a : G), q * x = x * q) : x ∈ qCore (a : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : IsPGroup 2 (Subgroup.zpowers (a : G)) :=
    (isPGroup_blockU S).to_le (Subgroup.zpowers_le.mpr a.2)
  have hD1 : Subgroup.zpowers (a : G) ≠ ⊥ := fun h =>
    ha1 (Subtype.ext (Subgroup.zpowers_eq_bot.mp h))
  have hchar := CFSG.CGT.PushingUpLit.T2K.isCharacteristicP_centralizer S.charTwo hD hD1
  rw [centralizer_zpowers_eq] at hchar
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩,
    hchar (Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_), rfl⟩
  exact hc _ (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

theorem exists_mem_J_lin_eq (hZ : blockZ J = ⊥) {a : ↥(blockU J)}
    {g : Vec m ≃ₗ[ZMod 2] Vec m} (hg : g ∈ rootGroup (quadQ m) (S.vec a)) :
    ∃ x : ↥M, (x : G) ∈ J ∧ (x : G) * (a : G) * (x : G)⁻¹ = a ∧ S.lin hZ x = g := by
  obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ
    (rootGroup_le_elementaryGroup (quadQ m) (S.vec a) hg)
  refine ⟨Subgroup.inclusion S.le ℓ, ℓ.2, (S.lin_vec_eq_iff hZ _ a).mp ?_, hℓ⟩
  rw [hℓ]
  obtain ⟨w, -, rfl⟩ := mem_rootGroup.mp hg
  exact eichler_apply_self _ _

theorem qCore_inf_le_rootSub (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) : qCore (a : G) ⊓ M ≤ rootSub S hZ a := by
  refine le_rootSub S hZ ha1 ha inf_le_right ((isPGroup_qCore _).to_le inf_le_left)
    (fun t ht => conj_eq_of_mem_centralizer (qCore_le_centralizer _ ht.1)) ?_
  intro ℓ hℓ hℓa t ht
  exact ⟨conj_mem_qCore (mem_centralizer_of_conj_eq hℓa) ht.1,
    M.mul_mem (M.mul_mem (S.le hℓ) ht.2) (M.inv_mem (S.le hℓ))⟩

theorem qCore_le_rootSub (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) : qCore (a : G) ≤ rootSub S hZ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : rootSub S hZ a ≤ Subgroup.normalizer (qCore (a : G) : Set G) :=
    (rootSub_le_centralizer S hZ a).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hY := IsPGroup.to_sup_of_normal_left' (isPGroup_qCore _)
    (isPGroup_rootSub S hH1 hZ hC a) hRn
  by_contra hle
  have hlt : rootSub S hZ a < qCore (a : G) ⊔ rootSub S hZ a :=
    lt_of_le_of_ne le_sup_right fun h => hle (le_sup_left.trans h.ge)
  obtain ⟨y, hyY, hyR, hyN⟩ := exists_mem_normalizer_of_lt hY hlt
  have hyM : y ∈ M := normalizer_perpSub_le S hH1 hZ hC ha1 ha
    (normalizer_rootSub_le S hH1 hZ hC ha1 ha hyN)
  have hyQR : y ∈ (qCore (a : G) : Set G) * (rootSub S hZ a : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRn]
    exact hyY
  obtain ⟨q, hq, r, hr, rfl⟩ := Set.mem_mul.mp hyQR
  have hqM : q ∈ M := by
    have h := M.mul_mem hyM (M.inv_mem (rootSub_le S hZ a hr))
    rwa [mul_inv_cancel_right] at h
  exact hyR ((rootSub S hZ a).mul_mem (qCore_inf_le_rootSub S hZ ha1 ha ⟨hq, hqM⟩) hr)

include S in
theorem centralizer_le_of_qCore_le_blockU {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (h : qCore (a : G) ≤ blockU J) : Subgroup.centralizer ({(a : G)} : Set G) ≤ M := by
  have hAQ : blockU J ≤ qCore (a : G) := fun u hu =>
    mem_qCore_of_commute S ha1
      (Subgroup.mem_centralizer_singleton_iff.mpr (Setting.blockU_comm S hu a.2))
      fun q hq => Setting.blockU_comm S (h hq) hu
  have heq : qCore (a : G) = blockU J := le_antisymm h hAQ
  intro g hg
  rw [← Setting.normalizer_blockU_eq S, ← heq]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg

theorem qCore_lin_surjective (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    ∀ g ∈ rootGroup (quadQ m) (S.vec a), ∃ y : ↥M, (y : G) ∈ qCore (a : G) ∧ S.lin hZ y = g := by
  rcases rootSub_dichotomy S hH1 hZ hC ha1 ha (qCore_le_rootSub S hH1 hZ hC ha1 ha)
    (fun ℓ _ hℓa y hy => conj_mem_qCore (mem_centralizer_of_conj_eq hℓa) hy) with h | h
  · exact absurd (centralizer_le_of_qCore_le_blockU S ha1 h) hnot
  · exact h

theorem exists_mul_of_mem_rootSub (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M)
    {r : G} (hr : r ∈ rootSub S hZ a) : ∃ u ∈ blockU J, ∃ q ∈ qCore (a : G), r = u * q := by
  obtain ⟨hrM, hrR⟩ := (mem_rootSub S).mp hr
  obtain ⟨y, hyQ, hy⟩ := qCore_lin_surjective S hH1 hZ hC ha1 ha hnot _ hrR
  have h1 : S.lin hZ (⟨r, hrM⟩ * y⁻¹) = 1 := by rw [map_mul, map_inv, hy, mul_inv_cancel]
  exact ⟨_, (lin_eq_one_iff_mem S hH1 hZ hC _).mp h1, y, hyQ, by simp⟩

theorem perpSub_le_of_mem (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {Y : Subgroup G} (haY : (a : G) ∈ Y)
    (hYn : ∀ ℓ ∈ J, ℓ * (a : G) * ℓ⁻¹ = a → ∀ y ∈ Y, ℓ * y * ℓ⁻¹ ∈ Y) {u : G} (huY : u ∈ Y)
    (huA : u ∈ blockU J) (hu : ¬ (u = 1 ∨ u = a)) : perpSub S a ≤ Y := by
  have hYn' : ∀ ℓ ∈ J, ℓ * (a : G) * ℓ⁻¹ = a →
      ∀ y ∈ Y ⊓ perpSub S a, ℓ * y * ℓ⁻¹ ∈ Y ⊓ perpSub S a :=
    fun ℓ hℓ hℓa y hy => ⟨hYn ℓ hℓ hℓa y hy.1, conj_mem_perpSub S hZ (S.le hℓ) hℓa hy.2⟩
  rcases perpSub_dichotomy S hZ ha1 ha (Y := Y ⊓ perpSub S a) ⟨haY, mem_perpSub_self S ha⟩
    (fun g hg => hg.1.2) hYn' with h | h
  · exfalso
    have hu0 : polar (quadQ m) (S.vec ⟨u, huA⟩) (S.vec a) ≠ 0 := fun h0 =>
      hu (h u ⟨⟨huY, (mem_perpSub_iff S ⟨u, huA⟩).mpr h0⟩, huA⟩)
    obtain ⟨g, hg, hg1⟩ := exists_mem_rootGroup_ne_one (nondegenerate_quadQ m) ha
      (vec_ne_zero S hZ ha1) (le_trans (by norm_num) (five_le_finrank S))
    obtain ⟨x, hxJ, hxa, rfl⟩ := exists_mem_J_lin_eq S hZ hg
    have hmem := commutator_mem_blockU_of_mem S x.2 huA
    have hvec := vec_commutator S hZ x ⟨u, huA⟩ hmem
    have hga : S.lin hZ x (S.vec a) = S.vec a := (S.lin_vec_eq_iff hZ x a).mpr hxa
    have hk : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Y ⊓ perpSub S a := by
      refine ⟨Y.mul_mem (hYn _ hxJ hxa u huY) (Y.inv_mem huY),
        (mem_perpSub_iff S ⟨_, hmem⟩).mpr ?_⟩
      rw [hvec]
      exact polar_sub_eq_zero (S.lin_mem_orthogonalGroup hZ x) hga _
    have hspan := (vec_mem_span_iff S hZ ⟨_, hmem⟩).mpr (h _ ⟨hk, hmem⟩)
    rw [hvec] at hspan
    exact sub_not_mem_span_of_mem_rootGroup (nondegenerate_quadQ m) ha hg hg1 hu0 hspan
  · exact fun g hg => (h hg).1

theorem perpSub_le_qCore (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    perpSub S a ≤ qCore (a : G) := by
  obtain ⟨g, hg, hg1⟩ := exists_mem_rootGroup_ne_one (nondegenerate_quadQ m) ha
    (vec_ne_zero S hZ ha1) (le_trans (by norm_num) (five_le_finrank S))
  obtain ⟨y, hyQ, rfl⟩ := qCore_lin_surjective S hH1 hZ hC ha1 ha hnot g hg
  obtain ⟨z, hz⟩ := exists_polar_ne_zero (nondegenerate_quadQ m) (vec_ne_zero S hZ ha1)
  obtain ⟨c, rfl⟩ := S.vec_surjective z
  have hc0 : polar (quadQ m) (S.vec c) (S.vec a) ≠ 0 := by rwa [polar_comm]
  have hmem := commutator_mem_blockU_of_mem S y.2 c.2
  have hcC : (c : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Setting.blockU_comm S c.2 a.2)
  have hkQ : (y : G) * c * (y : G)⁻¹ * (c : G)⁻¹ ∈ qCore (a : G) := by
    have h := (qCore (a : G)).mul_mem hyQ (conj_mem_qCore hcC ((qCore (a : G)).inv_mem hyQ))
    rwa [show (y : G) * ((c : G) * (y : G)⁻¹ * (c : G)⁻¹) =
      (y : G) * c * (y : G)⁻¹ * (c : G)⁻¹ by group] at h
  refine perpSub_le_of_mem S hZ ha1 ha (mem_qCore_self S a)
    (fun ℓ _ hℓa q hq => conj_mem_qCore (mem_centralizer_of_conj_eq hℓa) hq) hkQ hmem ?_
  intro hk
  have hspan := (vec_mem_span_iff S hZ ⟨_, hmem⟩).mpr hk
  rw [vec_commutator S hZ y c hmem] at hspan
  exact sub_not_mem_span_of_mem_rootGroup (nondegenerate_quadQ m) ha hg hg1 hc0 hspan

theorem not_blockU_le_qCore (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    ¬ blockU J ≤ qCore (a : G) := by
  intro hAQ
  apply hnot
  have hRQ : rootSub S hZ a ≤ qCore (a : G) := by
    intro r hr
    obtain ⟨u, hu, q, hq, rfl⟩ := exists_mul_of_mem_rootSub S hH1 hZ hC ha1 ha hnot hr
    exact (qCore (a : G)).mul_mem (hAQ hu) hq
  have heq : qCore (a : G) = rootSub S hZ a :=
    le_antisymm (qCore_le_rootSub S hH1 hZ hC ha1 ha) hRQ
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (rootSub S hZ a : Set G) :=
    heq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg
  exact normalizer_perpSub_le S hH1 hZ hC ha1 ha (normalizer_rootSub_le S hH1 hZ hC ha1 ha hgN)

theorem qCore_inf_blockU (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    qCore (a : G) ⊓ blockU J = perpSub S a := by
  have hA₁Q := perpSub_le_qCore S hH1 hZ hC ha1 ha hnot
  refine le_antisymm ?_ (le_inf hA₁Q (perpSub_le_blockU S a))
  rintro u ⟨huQ, huA⟩
  by_contra hu
  have hu0 : polar (quadQ m) (S.vec ⟨u, huA⟩) (S.vec a) ≠ 0 := fun h =>
    hu ((mem_perpSub_iff S ⟨u, huA⟩).mpr h)
  apply not_blockU_le_qCore S hH1 hZ hC ha1 ha hnot
  intro w hw
  by_cases hw0 : polar (quadQ m) (S.vec ⟨w, hw⟩) (S.vec a) = 0
  · exact hA₁Q ((mem_perpSub_iff S ⟨w, hw⟩).mpr hw0)
  · have hwu : w * u⁻¹ ∈ perpSub S a := by
      refine ⟨(blockU J).mul_mem hw ((blockU J).inv_mem huA), ?_⟩
      rw [show (⟨w * u⁻¹, (blockU J).mul_mem hw ((blockU J).inv_mem huA)⟩ : ↥(blockU J)) =
          ⟨w, hw⟩ * (⟨u, huA⟩ : ↥(blockU J))⁻¹ from rfl, S.vec_mul, vec_inv, polar_add_left,
        polar_neg_left, zmod2_eq_one_of_ne_zero hw0, zmod2_eq_one_of_ne_zero hu0]
      exact add_neg_cancel 1
    have h := (qCore (a : G)).mul_mem (hA₁Q hwu) huQ
    rwa [inv_mul_cancel_right] at h

theorem card_qCore (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    Nat.card (qCore (a : G)) = 2 ^ (1 + 2 * (2 * m)) := by
  have hQR := qCore_le_rootSub S hH1 hZ hC ha1 ha
  have hQM : qCore (a : G) ≤ M := hQR.trans (rootSub_le S hZ a)
  have hQA := qCore_inf_blockU S hH1 hZ hC ha1 ha hnot
  let f : ↥(qCore (a : G)) →* (Vec m ≃ₗ[ZMod 2] Vec m) := (S.lin hZ).comp (Subgroup.inclusion hQM)
  have hf : ∀ x : ↥(qCore (a : G)), f x = S.lin hZ ⟨x, hQM x.2⟩ := fun _ => rfl
  have hrange : f.range = rootGroup (quadQ m) (S.vec a) := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      rw [hf]
      exact ((mem_rootSub S).mp (hQR y.2)).2
    · intro hg
      obtain ⟨y, hyQ, hy⟩ := qCore_lin_surjective S hH1 hZ hC ha1 ha hnot g hg
      exact ⟨⟨y, hyQ⟩, by rw [hf]; exact hy⟩
  have hmemA : ∀ x : ↥(qCore (a : G)), x ∈ f.ker ↔ (x : G) ∈ perpSub S a := by
    intro x
    rw [MonoidHom.mem_ker, hf, lin_eq_one_iff_mem S hH1 hZ hC, ← hQA]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hker : Nat.card f.ker = Nat.card (perpSub S a) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨((x : ↥(qCore (a : G))) : G),
      (hmemA x).mp x.2⟩) ⟨fun x y hxy => ?_, fun w => ?_⟩)
    · exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
    · have hwQ : (w : G) ∈ qCore (a : G) := (hQA.ge w.2).1
      exact ⟨⟨⟨w, hwQ⟩, (hmemA ⟨w, hwQ⟩).mpr w.2⟩, rfl⟩
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, card_perpSub S hZ ha1,
    card_rootGroup (nondegenerate_quadQ m) ha (vec_ne_zero S hZ ha1), Nat.card_zmod,
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus, ← pow_add] at hcard
  rw [← hcard]
  congr 1
  omega

theorem isExtraspecial_qCore (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    IsExtraspecialPGroup 2 (qCore (a : G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hQR := qCore_le_rootSub S hH1 hZ hC ha1 ha
  have hQM : qCore (a : G) ≤ M := hQR.trans (rootSub_le S hZ a)
  have hQA := qCore_inf_blockU S hH1 hZ hC ha1 ha hnot
  have hA₁Q := perpSub_le_qCore S hH1 hZ hC ha1 ha hnot
  have hcenter : ∀ x ∈ qCore (a : G), (∀ y ∈ qCore (a : G), x * y = y * x) ↔
      x = 1 ∨ x = a := by
    intro x hx
    constructor
    · intro hc
      have hxA : x ∈ blockU J := mem_blockU_of_centralizer_perpSub S hH1 hZ hC ha (hQM hx)
        fun u hu => by rw [hc u (hA₁Q hu), mul_inv_cancel_right]
      refine eq_one_or_eq_of_commute_rootSub S hZ ha1 ha hxA fun r hr => ?_
      obtain ⟨u, hu, q, hq, rfl⟩ := exists_mul_of_mem_rootSub S hH1 hZ hC ha1 ha hnot hr
      rw [mul_assoc, ← hc q hq, ← mul_assoc, Setting.blockU_comm S hu hxA, mul_assoc]
    · rintro (rfl | rfl) y hy
      · rw [one_mul, mul_one]
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (qCore_le_centralizer _ hy)).symm
  let D : Subgroup G := Subgroup.closure {k | ∃ x ∈ qCore (a : G), ∃ y ∈ qCore (a : G),
    k = x * y * x⁻¹ * y⁻¹ ∨ k = x ^ 2}
  have hDsub : D ≤ perpSub S a := by
    rw [Subgroup.closure_le, ← hQA]
    rintro k ⟨x, hx, y, hy, rfl | rfl⟩
    · exact ⟨(qCore (a : G)).mul_mem ((qCore (a : G)).mul_mem ((qCore (a : G)).mul_mem hx hy)
        ((qCore (a : G)).inv_mem hx)) ((qCore (a : G)).inv_mem hy),
        commutator_mem_blockU S hH1 hZ hC (hQR hx) (hQR hy)⟩
    · exact ⟨(qCore (a : G)).pow_mem hx 2, by
        rw [pow_two]
        exact mul_self_mem_blockU S hH1 hZ hC (hQR hx)⟩
  have hDn : ∀ g ∈ Subgroup.centralizer ({(a : G)} : Set G), ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    induction hd using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨x, hx, y, hy, rfl | rfl⟩ := hk
      · exact Subgroup.subset_closure ⟨g * x * g⁻¹, conj_mem_qCore hg hx, g * y * g⁻¹,
          conj_mem_qCore hg hy, Or.inl (by group)⟩
      · exact Subgroup.subset_closure ⟨g * x * g⁻¹, conj_mem_qCore hg hx, 1,
          (qCore (a : G)).one_mem, Or.inr (by rw [pow_two, pow_two]; group)⟩
    | one => rw [mul_one, mul_inv_cancel]; exact D.one_mem
    | mul x y _ _ hx hy =>
      have h := D.mul_mem hx hy
      rwa [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at h
    | inv x _ hx =>
      have h := D.inv_mem hx
      rwa [show (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ by group] at h
  let Y : Subgroup G := D ⊔ Subgroup.zpowers (a : G)
  have hYle : Y ≤ perpSub S a := sup_le hDsub (Subgroup.zpowers_le.mpr (mem_perpSub_self S ha))
  have hYn : ∀ g ∈ Subgroup.centralizer ({(a : G)} : Set G), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg
    have hle : Y ≤ Y.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun d hd => ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_sup_left (hDn g hg d hd)
      · change g * (a : G) * g⁻¹ ∈ Y
        rw [conj_eq_of_mem_centralizer hg]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact fun y hy => hle hy
  rcases perpSub_dichotomy S hZ ha1 ha (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (fun g hg => hYle hg.1)
      (fun ℓ _ hℓa y hy => hYn ℓ (mem_centralizer_of_conj_eq hℓa) y hy) with h | h
  · have hD : ∀ d ∈ D, d = 1 ∨ d = a := fun d hd =>
      h d ⟨Subgroup.mem_sup_left hd, perpSub_le_blockU S a (hDsub hd)⟩
    refine CFSG.LargeExtraspecial.isExtraspecialPGroup_two_of_center (isPGroup_qCore _)
      (mem_qCore_self S a) ha1' hcenter
      (fun x hx y hy => hD _ (Subgroup.subset_closure ⟨x, hx, y, hy, Or.inl rfl⟩))
      (fun x hx => hD _ (Subgroup.subset_closure ⟨x, hx, 1, (qCore (a : G)).one_mem, Or.inr rfl⟩))
      ?_
    by_contra hab
    push Not at hab
    have hle : qCore (a : G) ≤ Subgroup.zpowers (a : G) := by
      intro x hx
      rcases (hcenter x hx).mp (hab x hx) with rfl | rfl
      · exact (Subgroup.zpowers _).one_mem
      · exact Subgroup.mem_zpowers _
    have hcard := Subgroup.card_le_of_le hle
    rw [card_qCore S hH1 hZ hC ha1 ha hnot, Nat.card_zpowers,
      orderOf_eq_prime (S.elemU.2 a a.2) ha1'] at hcard
    have hm : 1 ≤ m := by rcases S.m_eq with h | h <;> omega
    have h4 : 2 ^ 2 ≤ 2 ^ (1 + 2 * (2 * m)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exfalso
    apply hnot
    intro g hg
    have hY : Y = perpSub S a := le_antisymm hYle h
    refine normalizer_perpSub_le S hH1 hZ hC ha1 ha ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← hY]
    refine ⟨hYn g hg y, fun hy' => ?_⟩
    have h' := hYn g⁻¹ (Subgroup.inv_mem _ hg) _ hy'
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h'

theorem isExtraspecial_of_not_le_vec (hH1 : H1Natural m)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({(a : G)} : Set G))) ∧
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({(a : G)} : Set G))) =
        2 ^ (1 + 2 * (2 * m)) := by
  have hZ := S.blockZ_eq_bot hH1
  have heq : inSubgroup generalizedFitting (Subgroup.centralizer ({(a : G)} : Set G)) =
      qCore (a : G) := by
    have hcent := S.cent (Setting.blockU_le_pCoreOf S a.2) (fun h => ha1 (Subtype.ext h))
    unfold CFSG.inSubgroup qCore CFSG.Open.pCoreOf
    rw [hcent]
  rw [heq]
  exact ⟨isExtraspecial_qCore S hH1 hZ hC ha1 ha hnot, card_qCore S hH1 hZ hC ha1 ha hnot⟩

open Matrix in
theorem vec_eq_of_singular (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (Multiplicative.toAdd (S.beta a)) = 0) :
    S.vec a = Multiplicative.toAdd (S.beta a) := by
  have hw0 : Multiplicative.toAdd (S.beta a) ≠ 0 := by
    intro h
    apply ha1
    apply S.beta_injective hZ
    rw [map_one]
    exact Multiplicative.toAdd.injective (h.trans toAdd_one.symm)
  have hfix : ∀ g ∈ rootGroup (quadQ m) (Multiplicative.toAdd (S.beta a)),
      g (S.vec a) = S.vec a := by
    intro g hg
    obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ
      (rootGroup_le_elementaryGroup _ _ hg)
    have hgw : g (Multiplicative.toAdd (S.beta a)) = Multiplicative.toAdd (S.beta a) := by
      obtain ⟨w', -, rfl⟩ := mem_rootGroup.mp hg
      exact eichler_apply_self _ _
    have h1 : Multiplicative.toAdd (S.beta ⟨(ℓ : G) * a * (ℓ : G)⁻¹,
        Setting.conj_mem_blockU S (S.le ℓ.2) a.2⟩) = Multiplicative.toAdd (S.beta a) :=
      calc Multiplicative.toAdd (S.beta ⟨(ℓ : G) * a * (ℓ : G)⁻¹,
            Setting.conj_mem_blockU S (S.le ℓ.2) a.2⟩)
          = ((S.rho hZ (Subgroup.inclusion S.le ℓ) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
              Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
              Multiplicative.toAdd (S.beta a) :=
            (S.rho_mulVec hZ (Subgroup.inclusion S.le ℓ) a).symm
        _ = S.lin hZ (Subgroup.inclusion S.le ℓ) (Multiplicative.toAdd (S.beta a)) :=
            (S.lin_apply hZ _ _).symm
        _ = Multiplicative.toAdd (S.beta a) := by rw [hℓ, hgw]
    have h2 : (ℓ : G) * a * (ℓ : G)⁻¹ = a :=
      congrArg Subtype.val (S.beta_injective hZ (Multiplicative.toAdd.injective h1))
    rw [← hℓ]
    exact (S.lin_vec_eq_iff hZ _ a).mpr h2
  by_contra hne
  have hns : S.vec a ∉ (ZMod 2) ∙ Multiplicative.toAdd (S.beta a) := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul] at hc
      exact vec_ne_zero S hZ ha1 hc.symm
    · rw [one_smul] at hc
      exact hne hc.symm
  obtain ⟨g, hg, hgne⟩ := exists_mem_rootGroup_apply_ne (nondegenerate_quadQ m) ha hw0
    (le_trans (by norm_num) (five_le_finrank S)) hns
  exact hgne (hfix g hg)

end CFSG.CGT.HaradaParrott80

namespace CFSG.CGT.Harada80

open CFSG CFSG.QuasithinUnique

theorem Setting.isExtraspecial_of_not_le {G : Type} [Group G] [Finite G]
    {M J : Subgroup G} {m : ℕ} (S : Setting G M J m) (hH1 : H1Natural m)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (Multiplicative.toAdd (S.beta a)) = 0)
    (hnot : ¬ Subgroup.centralizer ({(a : G)} : Set G) ≤ M) :
    IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({(a : G)} : Set G))) ∧
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({(a : G)} : Set G))) =
        2 ^ (1 + 2 * (2 * m)) :=
  HaradaParrott80.isExtraspecial_of_not_le_vec S hH1 hC ha1
    (by rw [HaradaParrott80.vec_eq_of_singular S (S.blockZ_eq_bot hH1) ha1 ha]; exact ha) hnot

end CFSG.CGT.Harada80
