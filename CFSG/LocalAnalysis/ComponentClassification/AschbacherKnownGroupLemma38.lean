module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma35
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupTwoGroup
public import CFSG.LocalAnalysis.ComponentInitial.TwoGroupAction
public import CFSG.Walter.W67.CentralExt
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma38

variable {G : Type*} [Group G]

theorem isFourGroup_closure_pair [Finite G] {x y : G} (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) (hc : x * y = y * x) :
    IsFourGroup (closure ({x, y} : Set G)) := by
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hyy : y * y = 1 := by rw [← pow_two]; exact hy2
  have hxx' : ∀ w : G, x * (x * w) = w := fun w => by rw [← mul_assoc, hxx, one_mul]
  have hyy' : ∀ w : G, y * (y * w) = w := fun w => by rw [← mul_assoc, hyy, one_mul]
  have hyx : y * x = x * y := hc.symm
  have hyx' : ∀ w : G, y * (x * w) = x * (y * w) := fun w => by
    rw [← mul_assoc, hyx, mul_assoc]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  let K : Subgroup G :=
    { carrier := {1, x, y, x * y}
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp [mul_assoc, hxx, hyy, hxx', hyx, hyx']
      one_mem' := by simp
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl) <;> simp [hxi, hyi, hyx] }
  have hK : closure ({x, y} : Set G) = K := by
    apply le_antisymm
    · rw [closure_le]
      intro a ha
      rcases ha with rfl | rfl
      · change a ∈ ({1, a, y, a * y} : Set G)
        simp
      · change a ∈ ({1, x, a, x * a} : Set G)
        simp
    · intro a ha
      change a ∈ ({1, x, y, x * y} : Set G) at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  rw [hK]
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    change a ∈ ({1, x, y, x * y} : Set G) at ha
    change b ∈ ({1, x, y, x * y} : Set G) at hb
    change a * b = b * a
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, hxx, hyy, hxx', hyx, hyx']
  · intro a ha
    change a ∈ ({1, x, y, x * y} : Set G) at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [pow_two, mul_assoc, hxx, hyy, hyx']
  · change Nat.card ((K : Subgroup G) : Set G) = 4
    change Nat.card ({1, x, y, x * y} : Set G) = 4
    rw [Nat.card_coe_set_eq]
    have h1x : (1 : G) ≠ x := fun h => hx1 h.symm
    have h1y : (1 : G) ≠ y := fun h => hy1 h.symm
    have h1xy : (1 : G) ≠ x * y := by
      intro h
      apply hxy
      calc x = x * (x * y) := by rw [← h, mul_one]
        _ = y := hxx' y
    have hxxy : x ≠ x * y := by
      intro h
      apply hy1
      calc y = x * (x * y) := (hxx' y).symm
        _ = x * x := by rw [← h]
        _ = 1 := hxx
    have hyxy : y ≠ x * y := by
      intro h
      apply hx1
      calc x = x * (y * y) := by rw [hyy, mul_one]
        _ = (x * y) * y := by group
        _ = y * y := by rw [← h]
        _ = 1 := hyy
    rw [Set.ncard_insert_of_notMem (by simp [h1x, h1y, h1xy]),
      Set.ncard_insert_of_notMem (by simp [hxy, hxxy]), Set.ncard_pair hyxy]

theorem two_le_pRank_of_fourGroup [Finite G] {E H : Subgroup G} (hE : IsFourGroup E)
    (hEH : E ≤ H) : 2 ≤ Open.pRank 2 H :=
  SectionRank.le_pRank (by norm_num) hEH hE.1 (by rw [hE.2]; norm_num)

theorem pRank_sylow_map [Finite G] {A : Subgroup G} (T : Sylow 2 A) :
    Open.pRank 2 ((T : Subgroup A).map A.subtype) = Open.pRank 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (SectionRank.pRank_sylow T).1
  rw [← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  have hT : ((T : Subgroup A).map A.subtype).subgroupOf A = T :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  rw [← h1, ← RankThreeEvenClassification.Helpers.pRank_subgroupOf 2 Nat.prime_two _ A
    (map_subtype_le _), hT]

theorem two_le_pRank_centralizer_involution [Finite G] {A : Subgroup G}
    (hA : 2 ≤ Open.pRank 2 A) {a : G} (haA : a ∈ A) (ha2 : a ^ 2 = 1) :
    2 ≤ Open.pRank 2 (A ⊓ centralizer ({a} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases ha1 : a = 1
  · subst ha1
    rw [show centralizer ({(1 : G)} : Set G) = ⊤ by
      ext x; simp [mem_centralizer_singleton_iff], inf_top_eq]
    exact hA
  set a' : A := ⟨a, haA⟩ with ha'
  have ha'2 : a' ^ 2 = 1 := Subtype.ext (by simpa using ha2)
  have hp : IsPGroup 2 (zpowers a') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    exact ⟨1, by rw [pow_one]; exact orderOf_eq_prime ha'2 (fun h => ha1 (congrArg Subtype.val h))⟩
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have haT : a' ∈ (T : Subgroup A) := hT (mem_zpowers a')
  set T' := (T : Subgroup A).map A.subtype with hT'
  have hT'A : T' ≤ A := map_subtype_le _
  have hrank : Open.pRank 2 T' = Open.pRank 2 A := pRank_sylow_map T
  by_cases hcen : (⟨a', haT⟩ : (T : Subgroup A)) ∈ center (T : Subgroup A)
  ·
    apply le_trans hA
    rw [← hrank]
    apply SectionRank.pRank_mono (by norm_num)
    rintro x ⟨t, ht, rfl⟩
    refine mem_inf.2 ⟨t.2, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_center_iff.1 hcen ⟨t, ht⟩
    exact congrArg (fun w : (T : Subgroup A) => ((w : A) : G)) this
  ·
    have hTnt : Nontrivial (T : Subgroup A) := by
      refine ⟨⟨⟨a', haT⟩, 1, fun h => ha1 ?_⟩⟩
      exact congrArg (fun w : (T : Subgroup A) => ((w : A) : G)) h
    have hTp : IsPGroup 2 (T : Subgroup A) := T.isPGroup'
    have hZnt : Nontrivial (center (T : Subgroup A)) := hTp.center_nontrivial
    have h2Z : 2 ∣ Nat.card (center (T : Subgroup A)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hTp.to_subgroup (center (T : Subgroup A)))
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact (Finite.one_lt_card (α := center (T : Subgroup A))).ne' hk
      rw [hk]
      exact dvd_pow_self 2 hk0
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := center (T : Subgroup A)) 2 h2Z
    set z : G := (((z₀ : (T : Subgroup A)) : A) : G) with hz
    have hzo : orderOf z = 2 := by
      rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hz₀
    have hz2 : z ^ 2 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo
      norm_num at hzo
    have hza : z * a = a * z := by
      have := mem_center_iff.1 z₀.2 ⟨a', haT⟩
      exact (congrArg (fun w : (T : Subgroup A) => ((w : A) : G)) this).symm
    have hazne : a ≠ z := by
      intro h
      apply hcen
      have : (⟨a', haT⟩ : (T : Subgroup A)) = (z₀ : (T : Subgroup A)) := by
        apply Subtype.ext
        apply Subtype.ext
        exact h
      rw [this]
      exact z₀.2
    have hzA : z ∈ A := ((z₀ : (T : Subgroup A)) : A).2
    have hE := isFourGroup_closure_pair ha2 hz2 ha1 hz1 hazne hza.symm
    apply two_le_pRank_of_fourGroup hE
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact mem_inf.2 ⟨haA, mem_centralizer_singleton_iff.2 rfl⟩
    · exact mem_inf.2 ⟨hzA, mem_centralizer_singleton_iff.2 hza⟩

theorem two_le_pRank_centralizer_of_inner [Finite G] {A : Subgroup G}
    (hA : 2 ≤ Open.pRank 2 A) (hZ : (Nat.card (center A)).factorization 2 = 0) {u : G}
    (hu : u ∈ A ⊔ centralizer (A : Set G)) (hu2 : u ^ 2 = 1) :
    2 ≤ Open.pRank 2 (A ⊓ centralizer ({u} : Set G)) := by
  classical
  have hus : u ∈ ((A ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := hu
  rw [coe_mul_of_right_le_normalizer_left A (centralizer (A : Set G))
    (Subgroup.centralizer_le_normalizer (A : Set G))] at hus
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hus
  have hcA : ∀ x ∈ A, c * x = x * c := fun x hx => ((mem_centralizer_iff.1 hc) x hx).symm
  have hsame : ∀ b w : G, (∀ x ∈ A, x * w = w * x) →
      A ⊓ centralizer ({b * w} : Set G) = A ⊓ centralizer ({b} : Set G) := by
    intro b w hw
    ext x
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxu⟩
      refine ⟨hx, ?_⟩
      have : x * b * w = b * x * w := by
        calc x * b * w = x * (b * w) := by group
          _ = b * w * x := hxu
          _ = b * (w * x) := by group
          _ = b * (x * w) := by rw [hw x hx]
          _ = b * x * w := by group
      exact mul_right_cancel this
    · rintro ⟨hx, hxu⟩
      refine ⟨hx, ?_⟩
      calc x * (b * w) = (x * b) * w := by group
        _ = (b * x) * w := by rw [hxu]
        _ = b * (x * w) := by group
        _ = b * (w * x) := by rw [hw x hx]
        _ = b * w * x := by group
  have hac : a * c = c * a := (hcA a ha).symm
  have ha2 : a ^ 2 = (c ^ 2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc a ^ 2 * c ^ 2 = (a * c) * (a * c) := by
          rw [pow_two, pow_two]
          calc a * a * (c * c) = a * (a * c) * c := by group
            _ = a * (c * a) * c := by rw [hac]
            _ = a * c * (a * c) := by group
      _ = 1 := by rw [← pow_two]; exact hu2
  have ha2cen : ∀ x ∈ A, x * a ^ 2 = a ^ 2 * x := by
    intro x hx
    rw [ha2]
    have hc2 : c ^ 2 * x = x * c ^ 2 := by
      rw [pow_two]
      calc c * c * x = c * (c * x) := by group
        _ = c * (x * c) := by rw [hcA x hx]
        _ = (c * x) * c := by group
        _ = (x * c) * c := by rw [hcA x hx]
        _ = x * (c * c) := by group
    calc x * (c ^ 2)⁻¹ = (c ^ 2)⁻¹ * (c ^ 2 * x) * (c ^ 2)⁻¹ := by group
      _ = (c ^ 2)⁻¹ * (x * c ^ 2) * (c ^ 2)⁻¹ := by rw [hc2]
      _ = (c ^ 2)⁻¹ * x := by group
  have ha2A : a ^ 2 ∈ A := pow_mem ha 2
  have hcen : (⟨a ^ 2, ha2A⟩ : A) ∈ center A := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (ha2cen g g.2)
  obtain ⟨j, hj⟩ : ∃ j, Nat.card (center A) = 2 * j + 1 := by
    have hodd : Odd (Nat.card (center A)) := by
      rw [Nat.odd_iff]
      by_contra h
      have h2 : 2 ∣ Nat.card (center A) := Nat.dvd_of_mod_eq_zero (by omega)
      have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
      omega
    exact hodd
  have hpow : (a ^ 2) ^ (2 * j + 1) = 1 := by
    have h1 : (⟨⟨a ^ 2, ha2A⟩, hcen⟩ : center A) ^ Nat.card (center A) = 1 := pow_card_eq_one'
    rw [hj] at h1
    have := congrArg (fun w : center A => ((w : A) : G)) h1
    simpa using this
  have ha'2 : (a ^ (2 * j + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow]
  set w := ((a ^ 2) ^ j)⁻¹ with hw
  have hwcen : ∀ x ∈ A, x * w = w * x := by
    intro x hx
    have hx2j : x * (a ^ 2) ^ j = (a ^ 2) ^ j * x := ((Commute.pow_right (ha2cen x hx) j)).eq
    calc x * w = w * ((a ^ 2) ^ j * x) * w := by rw [hw]; group
      _ = w * (x * (a ^ 2) ^ j) * w := by rw [hx2j]
      _ = w * x := by rw [hw]; group
  have haw : a = a ^ (2 * j + 1) * w := by
    have hcomm : (a ^ 2) ^ j * a = a * (a ^ 2) ^ j := (((Commute.refl a).pow_left 2).pow_left j).eq
    rw [hw, pow_succ, pow_mul, hcomm, mul_inv_cancel_right]
  rw [hsame a c (fun x hx => (hcA x hx).symm), haw, hsame _ w hwcen]
  exact two_le_pRank_centralizer_involution hA (pow_mem ha _) ha'2

theorem even_card_of_isQuasisimple {K : Type*} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) : Even (Nat.card K) := by
  by_contra hodd
  exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
    (CatalogueBAlternating.quasisimple_iff_native.2 hK)
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 hodd))

theorem quasisimple_of_comparable [Finite G] {A : Subgroup G}
    (hA : aschbacherThm5IsSemisimple A) (S₀ : Sylow 2 A)
    (hcmp : ∀ Y₁ Y₂ : Subgroup G, Y₁ ≤ (S₀ : Subgroup A).map A.subtype →
      Y₂ ≤ (S₀ : Subgroup A).map A.subtype → ¬ IsCyclic Y₁ → ¬ IsCyclic Y₂ →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, y₁ * y₂ = y₂ * y₁) → Y₂ ≤ Y₁) :
    Open.IsQuasisimple A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, K, hk, hKq, hcomm, hsup⟩ := hA
  have hKA : ∀ i, K i ≤ A := fun i => (hKq i).1
  have hKN : ∀ i, A ≤ normalizer (K i : Set G) := by
    intro i
    rw [← hsup]
    apply iSup_le
    intro l
    by_cases hli : l = i
    · subst hli
      exact le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact (hcomm l i hli x hx y hy).symm
  by_cases hk1 : k = 1
  · subst hk1
    have hA0 : K 0 = A := by
      rw [← hsup, iSup_unique]
      rfl
    rw [← hA0]
    exact (hKq 0).2
  exfalso
  set i₀ : Fin k := ⟨0, by omega⟩
  set i₁ : Fin k := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hT : ∀ i, ∃ T : Sylow 2 (K i), ¬ IsCyclic ((T : Subgroup (K i)).map (K i).subtype) := by
    intro i
    have : Group.IsPerfect (K i) := ⟨(hKq i).2.1⟩
    let T : Sylow 2 (K i) := default
    refine ⟨T, fun hc => ?_⟩
    apply TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_perfect (K i)
      (even_card_of_isQuasisimple (hKq i).2) T
    exact ((T : Subgroup (K i)).equivMapOfInjective _ (K i).subtype_injective).isCyclic.2 hc
  obtain ⟨T₀, hT₀⟩ := hT i₀
  obtain ⟨T₁, hT₁⟩ := hT i₁
  set R₀ := (T₀ : Subgroup (K i₀)).map (K i₀).subtype with hR₀
  set R₁ := (T₁ : Subgroup (K i₁)).map (K i₁).subtype with hR₁
  have hR₀K : R₀ ≤ K i₀ := map_subtype_le _
  have hR₁K : R₁ ≤ K i₁ := map_subtype_le _
  have hRcomm : ∀ x ∈ R₀, ∀ y ∈ R₁, x * y = y * x :=
    fun x hx y hy => hcomm i₀ i₁ hi x (hR₀K hx) y (hR₁K hy)
  have hR₀p : IsPGroup 2 R₀ := T₀.isPGroup'.map _
  have hR₁p : IsPGroup 2 R₁ := T₁.isPGroup'.map _
  have hRp : IsPGroup 2 (R₀ ⊔ R₁ : Subgroup G) := by
    refine hR₀p.to_sup_of_normal_left' hR₁p ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact hRcomm x hx y hy
  have hRA : R₀ ⊔ R₁ ≤ A := sup_le (hR₀K.trans (hKA i₀)) (hR₁K.trans (hKA i₁))
  have hQp : IsPGroup 2 ((R₀ ⊔ R₁).subgroupOf A) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRA).symm
  obtain ⟨S₁, hS₁⟩ := hQp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S₁ S₀
  have hconjS : ∀ x ∈ R₀ ⊔ R₁, (g : G) * x * (g : G)⁻¹ ∈ (S₀ : Subgroup A).map A.subtype := by
    intro x hx
    have hxQ : (⟨x, hRA hx⟩ : A) ∈ (S₁ : Subgroup A) := hS₁ hx
    have hmem : g * ⟨x, hRA hx⟩ * g⁻¹ ∈ ((g • S₁ : Sylow 2 A) : Subgroup A) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨⟨x, hRA hx⟩, hxQ, by simp [MulAut.conj_apply]⟩
    rw [hg] at hmem
    exact ⟨_, hmem, rfl⟩
  let c := (MulAut.conj (g : G)).toMonoidHom
  set U₀ := R₀.map c with hU₀
  set U₁ := R₁.map c with hU₁
  have hcinj : Function.Injective c := (MulAut.conj (g : G)).injective
  have hU₀S : U₀ ≤ (S₀ : Subgroup A).map A.subtype := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconjS x (mem_sup_left hx)
  have hU₁S : U₁ ≤ (S₀ : Subgroup A).map A.subtype := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconjS x (mem_sup_right hx)
  have hU₀c : ¬ IsCyclic U₀ := fun h => hT₀ ((R₀.equivMapOfInjective c hcinj).isCyclic.2 h)
  have hU₁c : ¬ IsCyclic U₁ := fun h => hT₁ ((R₁.equivMapOfInjective c hcinj).isCyclic.2 h)
  have hUcomm : ∀ x ∈ U₀, ∀ y ∈ U₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change (g : G) * x * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) =
      (g : G) * y * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹)
    calc (g : G) * x * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) = (g : G) * (x * y) * (g : G)⁻¹ := by
          group
      _ = (g : G) * (y * x) * (g : G)⁻¹ := by rw [hRcomm x hx y hy]
      _ = (g : G) * y * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) := by group
  have h01 : U₀ ≤ U₁ := hcmp U₁ U₀ hU₁S hU₀S hU₁c hU₀c (fun x hx y hy => (hUcomm y hy x hx).symm)
  have hR₀K₁ : R₀ ≤ K i₁ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h01 (mem_map_of_mem c hx)
    rw [← hcinj hyx]
    exact hR₁K hy
  have hcen : (T₀ : Subgroup (K i₀)) ≤ center (K i₀) := by
    intro t ht
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have htK₁ : (t : G) ∈ K i₁ := hR₀K₁ ⟨t, ht, rfl⟩
    exact (hcomm i₀ i₁ hi x x.2 t htK₁)
  have hab : IsMulCommutative (T₀ : Subgroup (K i₀)) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact mem_center_iff.1 (hcen b.2) a
  have hbot := Walter.W67.inf_commutator_eq_bot_of_isPGroup T₀ hab hcen T₀.isPGroup'
  have : Group.IsPerfect (K i₀) := ⟨(hKq i₀).2.1⟩
  rw [Group.IsPerfect.commutator_eq_top, inf_top_eq] at hbot
  apply hT₀
  rw [hR₀, hbot, Subgroup.map_bot]
  infer_instance

theorem two_involutions_of_not_isCyclic {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {B : Subgroup P} (hBab : IsMulCommutative B) (hBc : ¬ IsCyclic B) :
    ∃ x y : P, x ∈ B ∧ y ∈ B ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup B :=
    { (inferInstance : Group B) with mul_comm := fun a b => isMulCommutative_iff.mp hBab a b }
  have hBp : IsPGroup 2 B := hP.to_subgroup B
  rw [RankTwoShapes.isCyclic_iff_subgroup_card_prime_unique hBp] at hBc
  push Not at hBc
  obtain ⟨B₁, B₂, h1, h2, hne⟩ := hBc
  have gen : ∀ C : Subgroup B, Nat.card C = 2 →
      ∃ x : B, x ∈ C ∧ x ≠ 1 ∧ x ^ 2 = 1 ∧ C = zpowers x := by
    intro C hC
    have hCne : C ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hC
      norm_num at hC
    obtain ⟨⟨x, hxC⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hCne
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hdvd : orderOf x ∣ 2 := by
      rw [← hC]
      exact Subgroup.orderOf_dvd_natCard C hxC
    have hx2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
    have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1'
    refine ⟨x, hxC, hx1', hx2, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxC)
    rw [Nat.card_zpowers, hord, hC]
  obtain ⟨x, -, hx1, hx2, hC1⟩ := gen B₁ h1
  obtain ⟨y, -, hy1, hy2, hC2⟩ := gen B₂ h2
  refine ⟨x, y, x.2, y.2, ?_, ?_, fun h => hx1 (Subtype.ext h), fun h => hy1 (Subtype.ext h),
    fun h => hne (by rw [hC1, hC2, Subtype.ext h])⟩
  · exact congrArg Subtype.val hx2
  · exact congrArg Subtype.val hy2

theorem exists_centralized_fourGroup {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {B U : Subgroup P} [B.Normal] (hBab : IsMulCommutative B) (hBc : ¬ IsCyclic B)
    (hU : Nat.card U = 4) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ z w : P, z ∈ B ∧ w ∈ B ∧ z ^ 2 = 1 ∧ w ^ 2 = 1 ∧ z ≠ 1 ∧ w ≠ 1 ∧
      z ≠ w ∧ z * w = w * z ∧ u * z = z * u ∧ u * w = w * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hBab ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x₁, x₂, hx₁, hx₂, ho₁, ho₂, h₁, h₂, hne⟩ := two_involutions_of_not_isCyclic hP hBab hBc
  let Ω : Subgroup P :=
    { carrier := {b | b ∈ B ∧ b ^ 2 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨B.mul_mem ha hb, ?_⟩
        rw [pow_two]
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hBcomm b hb a ha]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [← pow_two, ← pow_two, ha2, hb2, one_mul]
      one_mem' := ⟨B.one_mem, one_pow 2⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨B.inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have hΩn : Ω.Normal := by
    refine ⟨fun n hn g => ⟨‹B.Normal›.conj_mem n hn.1 g, ?_⟩⟩
    rw [conj_pow, hn.2]
    group
  have hΩne : Ω ≠ ⊥ := by
    intro h
    have : x₁ ∈ Ω := ⟨hx₁, ho₁⟩
    rw [h, mem_bot] at this
    exact h₁ this
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hΩne)
  obtain ⟨⟨hzB, hz2⟩, hzZ⟩ := mem_inf.1 hz
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  set Z := zpowers z with hZ
  have hZn : Z.Normal := normal_of_le_center (zpowers_le.2 hzZ)
  have hZmem : ∀ y : P, y ∈ Z ↔ y = 1 ∨ y = z := by
    intro y
    constructor
    · exact RankOne.mem_zpowers_of_sq hz2
    · rintro (h | h) <;> rw [h]
      · exact one_mem _
      · exact mem_zpowers _
  let q := QuotientGroup.mk' Z
  have hΩbar : Ω.map q ≠ ⊥ := by
    intro h
    have hle := (Subgroup.map_eq_bot_iff Ω).mp h
    rw [QuotientGroup.ker_mk'] at hle
    rcases (hZmem x₁).1 (hle ⟨hx₁, ho₁⟩) with h1 | h1
    · exact h₁ h1
    rcases (hZmem x₂).1 (hle ⟨hx₂, ho₂⟩) with h2 | h2
    · exact h₂ h2
    · exact hne (h1.trans h2.symm)
  have : (Ω.map q).Normal := Normal.map hΩn q (QuotientGroup.mk'_surjective Z)
  have hnil' : Group.IsNilpotent (P ⧸ Z) := (hP.to_quotient Z).isNilpotent
  obtain ⟨⟨wb, hwb⟩, hwb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hΩbar)
  obtain ⟨hwbΩ, hwbZ⟩ := mem_inf.1 hwb
  obtain ⟨w, ⟨hwB, hw2⟩, hwq⟩ := hwbΩ
  have hwZ : w ∉ Z := by
    intro h
    apply hwb1
    apply Subtype.ext
    change wb = 1
    rw [← hwq]
    exact (QuotientGroup.eq_one_iff w).2 h
  have hw1 : w ≠ 1 := fun h => hwZ (h ▸ one_mem Z)
  have hzw : z ≠ w := fun h => hwZ (h ▸ mem_zpowers z)
  have hconj : ∀ p : P, p * w * p⁻¹ = w ∨ p * w * p⁻¹ = w * z := by
    intro p
    have hc : q (p * w * p⁻¹ * w⁻¹) = 1 := by
      have := mem_center_iff.1 hwbZ (q p)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwq, this]
      group
    have hmem : p * w * p⁻¹ * w⁻¹ ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact hc
    rcases (hZmem _).1 hmem with h | h
    · left
      calc p * w * p⁻¹ = p * w * p⁻¹ * w⁻¹ * w := by group
        _ = w := by rw [h, one_mul]
    · right
      calc p * w * p⁻¹ = p * w * p⁻¹ * w⁻¹ * w := by group
        _ = z * w := by rw [h]
        _ = w * z := (hBcomm z hzB w hwB)
  let _ : Fintype U := Fintype.ofFinite U
  have hcard : Fintype.card Bool < Fintype.card U := by
    rw [Fintype.card_bool, ← Nat.card_eq_fintype_card, hU]
    norm_num
  obtain ⟨u₁, u₂, hu12, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun u : U => decide ((u : P) * w * (u : P)⁻¹ = w)) hcard
  have hsame : (u₁ : P) * w * (u₁ : P)⁻¹ = (u₂ : P) * w * (u₂ : P)⁻¹ := by
    by_cases h1 : (u₁ : P) * w * (u₁ : P)⁻¹ = w
    · have h2 : (u₂ : P) * w * (u₂ : P)⁻¹ = w := by simpa [h1] using hf.symm
      rw [h1, h2]
    · have h2 : ¬ (u₂ : P) * w * (u₂ : P)⁻¹ = w := by simpa [h1] using hf.symm
      rw [(hconj u₁).resolve_left h1, (hconj u₂).resolve_left h2]
  refine ⟨(u₂ : P)⁻¹ * u₁, U.mul_mem (U.inv_mem u₂.2) u₁.2, ?_, z, w, hzB, hwB, hz2, hw2, hz1',
    hw1, hzw, hBcomm z hzB w hwB, ?_, ?_⟩
  · intro h
    apply hu12
    apply Subtype.ext
    calc (u₁ : P) = (u₂ : P) * ((u₂ : P)⁻¹ * u₁) := by group
      _ = u₂ := by rw [h, mul_one]
  · exact mem_center_iff.1 hzZ _
  · calc (u₂ : P)⁻¹ * u₁ * w = (u₂ : P)⁻¹ * ((u₁ : P) * w * (u₁ : P)⁻¹) * u₁ := by group
      _ = (u₂ : P)⁻¹ * ((u₂ : P) * w * (u₂ : P)⁻¹) * u₁ := by rw [hsame]
      _ = w * ((u₂ : P)⁻¹ * u₁) := by group

end Lemma38

open Lemma38 in
theorem lemma_3_8 (hK : AschbacherKnownGroupFacts) {G : Type} [Group G] [Finite G]
    (A U : Subgroup G) (hA : aschbacherThm5IsSemisimple A)
    (hUA : U ≤ normalizer (A : Set G)) (hU : IsFourGroup U)
    (h : Open.pRank 2 (centralizerJoin U A) ≤ 1) : Open.pRank 2 A = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcj : ∀ u ∈ U, u ≠ 1 → Open.pRank 2 (A ⊓ centralizer ({u} : Set G)) ≤ 1 :=
    fun u hu hu1 => (SectionRank.pRank_mono (by norm_num)
      (Lemma35.inf_centralizer_le_centralizerJoin hu hu1)).trans h
  have hUp : IsPGroup 2 U := by
    rw [IsPGroup.iff_card, hU.2]
    exact ⟨2, by norm_num⟩
  obtain ⟨S₀, hS₀⟩ :=
    LocalAnalysis.ComponentInitial.TwoGroupAction.exists_sylow_le_normalizer hUp hUA
  set S := (S₀ : Subgroup A).map A.subtype with hS
  have hSA : S ≤ A := map_subtype_le _
  have hSp : IsPGroup 2 S := S₀.isPGroup'.map _
  have hrankS : Open.pRank 2 S = Open.pRank 2 A := pRank_sylow_map S₀
  set P := S ⊔ U with hP
  have hPp : IsPGroup 2 P := hSp.to_sup_of_normal_left' hUp hS₀
  have hSP : S ≤ P := le_sup_left
  have hUP : U ≤ P := le_sup_right
  have hPN : P ≤ normalizer (S : Set G) := sup_le le_normalizer hS₀
  set S' : Subgroup P := S.subgroupOf P with hS'
  have hS'n : S'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hPN g.2) n).1 hn
  have hcyc : ∀ B : Subgroup P, B ≤ S' → B.Normal → IsMulCommutative B → IsCyclic B := by
    intro B hBS hBn hBab
    by_contra hBc
    have hUcard : Nat.card (U.subgroupOf P) = 4 := by
      rw [← hU.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv
    obtain ⟨u, huU, hu1, z, w, hzB, hwB, hz2, hw2, hz1, hw1, hzw, hzwc, huz, huw⟩ :=
      exists_centralized_fourGroup (P := P) hPp hBab hBc hUcard
    have hzS : (z : G) ∈ S := hBS hzB
    have hwS : (w : G) ∈ S := hBS hwB
    have hE := isFourGroup_closure_pair (x := (z : G)) (y := (w : G))
      (by rw [← Subgroup.coe_pow, hz2]; rfl) (by rw [← Subgroup.coe_pow, hw2]; rfl)
      (fun h => hz1 (Subtype.ext h)) (fun h => hw1 (Subtype.ext h))
      (fun h => hzw (Subtype.ext h)) (congrArg Subtype.val hzwc)
    have hle : closure ({(z : G), (w : G)} : Set G) ≤ A ⊓ centralizer ({(u : G)} : Set G) := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact mem_inf.2 ⟨hSA hzS, mem_centralizer_singleton_iff.2 (congrArg Subtype.val huz).symm⟩
      · exact mem_inf.2 ⟨hSA hwS, mem_centralizer_singleton_iff.2 (congrArg Subtype.val huw).symm⟩
    have h2 := two_le_pRank_of_fourGroup hE hle
    have h1 := hcj u huU (fun h => hu1 (Subtype.ext h))
    omega
  by_cases hinv : ∃ x₁ x₂ : G, x₁ ∈ S ∧ x₂ ∈ S ∧ x₁ ^ 2 = 1 ∧ x₂ ^ 2 = 1 ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧
      x₁ ≠ x₂
  ·
    exfalso
    obtain ⟨x₁, x₂, hx₁, hx₂, ho₁, ho₂, h₁, h₂, hne⟩ := hinv
    obtain ⟨hshape, ⟨E, hES, hEab, hEexp, hEcard⟩, hcmp⟩ :=
      TwoGroup.dihedral_or_semidihedral_rel hPp S' hcyc (x₁ := ⟨x₁, hSP hx₁⟩)
        (x₂ := ⟨x₂, hSP hx₂⟩) hx₁ hx₂ (Subtype.ext (by simpa using ho₁))
        (Subtype.ext (by simpa using ho₂)) (fun h => h₁ (congrArg Subtype.val h))
        (fun h => h₂ (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
    have hA2 : 2 ≤ Open.pRank 2 A := by
      have hEG : IsFourGroup (E.map P.subtype) :=
        ⟨Lemma35.isElemAbelian_map ⟨hEab, hEexp⟩ P.subtype,
          by rw [card_map_of_injective P.subtype_injective, hEcard]⟩
      refine two_le_pRank_of_fourGroup hEG ?_
      rintro _ ⟨e, he, rfl⟩
      exact hSA (hES he)
    have hcmpG : ∀ Y₁ Y₂ : Subgroup G, Y₁ ≤ S → Y₂ ≤ S → ¬ IsCyclic Y₁ → ¬ IsCyclic Y₂ →
        (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, y₁ * y₂ = y₂ * y₁) → Y₂ ≤ Y₁ := by
      intro Y₁ Y₂ h1 h2 hc1 hc2 hcomm
      have hY₁P : Y₁ ≤ P := h1.trans hSP
      have hY₂P : Y₂ ≤ P := h2.trans hSP
      have key := hcmp (Y₁.subgroupOf P) (Y₂.subgroupOf P) (fun x hx => h1 hx)
        (fun x hx => h2 hx)
        (fun hc => hc1 ((Subgroup.subgroupOfEquivOfLe hY₁P).isCyclic.1 hc))
        (fun hc => hc2 ((Subgroup.subgroupOfEquivOfLe hY₂P).isCyclic.1 hc))
        (fun y₁ hy₁ y₂ hy₂ => Subtype.ext (hcomm y₁ hy₁ y₂ hy₂))
      intro y hy
      exact key (show (⟨y, hY₂P hy⟩ : P) ∈ Y₂.subgroupOf P from hy)
    have hAq : Open.IsQuasisimple A := quasisimple_of_comparable hA S₀ hcmpG
    have hiso : (S₀ : Subgroup A) ≃* (S' : Subgroup P) :=
      ((S₀ : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective).trans
        (Subgroup.subgroupOfEquivOfLe hSP).symm
    have hUne : U ≠ ⊥ := by
      intro hb
      have := hU.2
      rw [hb, card_bot] at this
      norm_num at this
    obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hUne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    ·
      have hD : HasDihedralSylowTwo A := ⟨S₀, n, hn, ⟨hiso.trans e⟩⟩
      obtain ⟨hDq, hZ⟩ := dihedral_quotient_center hAq hD
      have hgen : ¬ A ≤ centralizerJoin U A := fun hle => by
        have := SectionRank.pRank_mono (p := 2) (by norm_num) hle
        omega
      obtain ⟨-, hUle⟩ := hK.dihedral_cover_generation G A U hAq hDq (by omega) hUA hU hgen
      have h2 := two_le_pRank_centralizer_of_inner hA2 hZ (hUle huU) (hU.1.2 u huU)
      have h1 := hcj u huU hu1'
      omega
    ·
      have hSD : HasSemidihedralSylowTwo A := ⟨S₀, n, hn, ⟨hiso.trans e⟩⟩
      obtain ⟨u', hu'U, hu'1, hu'2⟩ := hK.semidihedral_four_group G A U hAq hSD hUA hU
      have := hcj u' hu'U hu'1
      omega
  ·
    push Not at hinv
    apply le_antisymm
    · rw [← hrankS]
      apply SectionRank.pRank_le (by norm_num)
      intro E hES hE
      by_cases hEb : E = ⊥
      · rw [hEb, card_bot]
        norm_num
      · obtain ⟨⟨e, heE⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEb
        have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
        have hle : E ≤ zpowers e := by
          intro x hx
          by_cases hx1 : x = 1
          · rw [hx1]
            exact one_mem _
          · rw [hinv x e (hES hx) (hES heE) (hE.2 x hx) (hE.2 e heE) hx1 he1']
            exact mem_zpowers e
        calc Nat.card E ≤ Nat.card (zpowers e) := card_le_of_le hle
          _ = 2 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime (hE.2 e heE) he1'
          _ = 2 ^ 1 := by norm_num
    ·
      obtain ⟨k, K, hk, hKq, -, -⟩ := hA
      have hev := even_card_of_isQuasisimple (hKq ⟨0, hk⟩).2
      have h2A : 2 ∣ Nat.card A :=
        (even_iff_two_dvd.1 hev).trans (Subgroup.card_dvd_of_le (hKq ⟨0, hk⟩).1)
      obtain ⟨⟨x, hxA⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2A
      have hxo : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxA]; exact hx
      have hx2 : x ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
      refine SectionRank.le_pRank (by norm_num) (zpowers_le.2 hxA) ⟨inferInstance, ?_⟩
        (by rw [Nat.card_zpowers, hxo]; norm_num)
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]

end CFSG.ComponentClassification.AschbacherKnownGroup
