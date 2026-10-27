module

public import CFSG.GH74.Generic.BProg.B1.Shapes
public import CFSG.GH74.Generic.BProg.B1.PilotS5Facts
public import CFSG.GH74.Generic.BProg.Stage2QSProofAbs
public import CFSG.GH74.GLS.TwoThin.Bridge
public import CFSG.RankThree.PartOne.KC.PlaneLifting

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS5

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.Walter CFSG.Walter.J1Props CFSG.Open
open scoped commutatorElement

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem hat_equiv_imgBar {x : G} {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(imgBar x K)) := by
  obtain ⟨hKC, Kb, -, hsub, -⟩ := hK
  obtain ⟨e1⟩ := TwoThin.hat_equiv_subgroupOf hKC
  obtain ⟨e2⟩ := TwoThin.hat_equiv_map (M := K.subgroupOf (centralizer ({x} : Set G))) hsub
  exact ⟨e1.trans e2⟩


theorem not_mem_of_center_trivial {x : G} {K : Subgroup G}
    (hx : orderOf x = 2) (hKC : K ≤ centralizer ({x} : Set G))
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1) : x ∉ K := by
  intro hxK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set k₀ : ↥K := ⟨x, hxK⟩ with hk₀
  have hc : ∀ k : ↥K, k * k₀ = k₀ * k := fun k =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hKC k.2))
  have h1 : (QuotientGroup.mk k₀ : ↥K ⧸ pPrimeCore 2 ↥K) = 1 := by
    apply hZ
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
  have h2 : k₀ ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff k₀).1 h1
  have h3 : orderOf k₀ ∣ Nat.card (pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ h2
  have h4 : orderOf k₀ = 2 := by rw [hk₀, Subgroup.orderOf_mk]; exact hx
  rw [h4] at h3
  have := (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)).eq_one_of_dvd h3
  omega

theorem xbar_not_mem_imgBar {x : G} {K : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K) : xbar x ∉ imgBar x K := by
  intro hmem
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have h2 : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    simpa using (by rw [← hx]; exact pow_orderOf_eq_one x : x ^ 2 = 1)
  have := mem_of_two_pow_eq_one_of_map_mem hK.2 h2 hmem
  exact hxK (Subgroup.mem_subgroupOf.1 this)

theorem orderOf_xbar {x : G} (hx : orderOf x = 2) : orderOf (xbar x) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact xbar_mul_self hx) (xbar_ne_one hx)

theorem bar_facts {x y : G} {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) (hyK : y ∈ K)
    (hy2 : orderOf y = 2) :
    bar x y ∈ imgBar x K ∧ bar x y ≠ 1 ∧ orderOf (bar x y) = 2 := by
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have h1 : bar x y = proj x ⟨y, hyC⟩ := bar_of_mem hyC
  have hne : bar x y ≠ 1 := by
    intro h
    have := proj_odd x ⟨y, hyC⟩ (by rw [← h1]; exact h)
    rw [Subgroup.orderOf_mk, hy2] at this
    exact absurd this (by decide)
  refine ⟨?_, hne, orderOf_eq_prime ?_ hne⟩
  · rw [h1]; exact mem_imgBar.2 ⟨⟨y, hyC⟩, hyK, rfl⟩
  · rw [h1, ← map_pow]
    have : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ^ 2 = 1 :=
      Subtype.ext (by rw [← hy2]; exact pow_orderOf_eq_one y)
    rw [this, map_one]

theorem bar_not_mem_zpowers_xbar {x y : G} {K : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K) (hyK : y ∈ K)
    (hy2 : orderOf y = 2) : bar x y ∉ zpowers (xbar x) := by
  intro hmem
  obtain ⟨h1, h2, -⟩ := bar_facts hK.1 hyK hy2
  rcases mem_zpowers_of_two (orderOf_xbar hx) hmem with h | h
  · exact h2 h
  · exact xbar_not_mem_imgBar hx hK hxK (h ▸ h1)


theorem exists_source_of_four {x : G} {K : Subgroup G}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1)
    (hV : ∃ V : Subgroup (↥K ⧸ pPrimeCore 2 ↥K), CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hshape : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨
      QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) : ∃ A : Subgroup G, IsSource2 x K A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hxK : x ∉ K := not_mem_of_center_trivial hx hKC hZ
  obtain ⟨V, hVel, hV4⟩ := hV
  set ψ : ↥K →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hψ
  have hker : ¬ 2 ∣ Nat.card ψ.ker := by
    rw [hψ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 CFSG.pPrimeCore_coprime_card
  have hVr : V ≤ ψ.range := by
    rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨E₀, hE₀el, hE₀4, -⟩ := CFSG.RankThree.PartOne.exists_lift_elementaryAbelian ψ
    Nat.prime_two hker V hVr (by rw [hV4]; norm_num)
  set E : Subgroup G := E₀.map K.subtype with hE
  have hEK : E ≤ K := Subgroup.map_subtype_le _
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := CFSG.IsElementaryAbelian.map_subtype
  have hE4 : Nat.card ↥E = 4 := by
    rw [hE, Subgroup.card_map_of_injective K.subtype_injective, hE₀4]; norm_num
  have hxE : x ∉ E := fun h => hxK (hEK h)
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  have hzE : zpowers x ≤ centralizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hKC (hEK he)))
  refine ⟨E ⊔ zpowers x, ?_, ?_, ?_, Or.inr ⟨E, hEK, rfl, hxE, hEel, hE4, hshape⟩⟩
  · exact sup_le (hEK.trans hKC) (Subgroup.zpowers_le.2 hxC)
  · exact CFSG.IsElementaryAbelian.sup_of_le_centralizer hzE
  · have hnorm : zpowers x ≤ Subgroup.normalizer (E : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ (hzE ha)
    have hdisj : Disjoint E (zpowers x) := by
      rw [Subgroup.disjoint_def]
      intro a haE hax
      rcases mem_zpowers_of_two hx hax with h | h
      · exact h
      · exact absurd (h ▸ haE) hxE
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (zpowers x) hnorm hdisj,
      Nat.card_zpowers, hx, hE4]

theorem exists_source_of_shape5 {x : G} {K : Subgroup G}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (h5 : QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) : ∃ A : Subgroup G, IsSource2 x K A :=
  exists_source_of_four hx hK (center_of_isSporadic h5) (exists_four_of_isSporadic h5)
    (Or.inr (Or.inr h5))

omit [Finite G] in
theorem closure_pair_facts {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hne : x ≠ y) :
    closure ({x, y} : Set G) = zpowers x ⊔ zpowers y ∧
      CFSG.IsElementaryAbelian 2 ↥(closure ({x, y} : Set G)) ∧
      Nat.card ↥(closure ({x, y} : Set G)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcl : closure ({x, y} : Set G) = zpowers x ⊔ zpowers y := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro a ha
      rcases ha with h | h
      · rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff.1 h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
        (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  have hyel : CFSG.IsElementaryAbelian 2 ↥(zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hy2
  have hyx : zpowers y ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (show Commute x y from hxy) k).eq)
  refine ⟨hcl, ?_, ?_⟩
  · rw [hcl]
    exact CFSG.IsElementaryAbelian.sup_of_le_centralizer hyx
  · rw [hcl]
    have hnorm : zpowers y ≤ Subgroup.normalizer ((zpowers x : Subgroup G) : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ (hyx ha)
    have hdisj : Disjoint (zpowers x) (zpowers y) := by
      rw [Subgroup.disjoint_def]
      intro a hax hay
      rcases mem_zpowers_of_two hx hax with h | h
      · exact h
      · rcases mem_zpowers_of_two hy hay with h' | h'
        · exact h'
        · exact absurd (h.symm.trans h') hne
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hx, hy]

theorem not_qShape1_of_qShape5 {Kt : Type} [Group Kt]
    (h1 : QShape1 Kt) (h5 : QShape5 Kt) : False := by
  have hc := IsSL4Model.natCard_center h1
  have hz : Subgroup.center Kt = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact center_of_isSporadic h5 z (fun g => Subgroup.mem_center_iff.1 hz g)
  rw [hz, Subgroup.card_bot] at hc
  omega


theorem exists_adm_of_split {n : ℕ} {x : G} {K A E : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K)
    (hY : SplitLike n (imgBar x K)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hEnt : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE4]; norm_num)
  obtain ⟨⟨y, hyE⟩, hy1⟩ := exists_ne (1 : ↥E)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyK : y ∈ K := hEK hyE
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hy2sq : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) y hyE
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy2sq hy1'
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxyne : x ≠ y := fun h => hxK (h ▸ hyK)
  obtain ⟨hDcl, hDel, hD4⟩ := closure_pair_facts hx hy2 hxy hxyne
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  obtain ⟨hbmem, hbne, hb2⟩ := bar_facts hKC hyK hy2
  obtain ⟨L, hLY, hL, hrel⟩ := hY.exists_pair hbmem hb2
  have hyne : bar x y ∉ zpowers (xbar x) := bar_not_mem_zpowers_xbar hx hK hxK hyK hy2
  have hDA : D ≤ A := by
    rw [hD, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h, hAE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · rw [Set.mem_singleton_iff.1 h, hAE]; exact Subgroup.mem_sup_left hyE
  have hDC : D ≤ centralizer ({x} : Set G) := by
    rw [hD, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · rw [Set.mem_singleton_iff.1 h]; exact hyC
  have hDrank : 2 ≤ pRank 2 ↥D := by
    have := CFSG.pRank_eq_of_card_eq_pow (A := ↥D) Nat.one_lt_two (k := 2) (by rw [hD4]; norm_num)
    omega
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hLD : L ≤ centralizer ((imgBar x D : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) := by
    set Q : Subgroup G := ((centralizer (L : Set (CentralizerBar x))).comap (proj x)).map
      (centralizer ({x} : Set G)).subtype with hQ
    have hxQ : x ∈ Q := ⟨⟨x, hxC⟩, by
      show proj x ⟨x, hxC⟩ ∈ centralizer (L : Set (CentralizerBar x))
      exact Subgroup.mem_centralizer_iff.2 fun l _ =>
        (Subgroup.mem_center_iff.1 (xbar_mem_center x)) l, rfl⟩
    have hyQ : y ∈ Q := ⟨⟨y, hyC⟩, by
      show proj x ⟨y, hyC⟩ ∈ centralizer (L : Set (CentralizerBar x))
      rw [← bar_of_mem hyC]
      exact Subgroup.mem_centralizer_iff.2 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.1 (hL.le_cent hl), rfl⟩
    have hDQ : D ≤ Q := by
      rw [hD, Subgroup.closure_le]
      intro a ha
      rcases ha with h | h
      · rw [h]; exact hxQ
      · rw [Set.mem_singleton_iff.1 h]; exact hyQ
    intro l hl
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    obtain ⟨c', hc', rfl⟩ := hg
    obtain ⟨c'', hc'', hcc⟩ := hDQ hc'
    have : c'' = c' := Subtype.ext hcc
    subst this
    exact (Subgroup.mem_centralizer_iff.1 hc'' l hl).symm
  have hLself : pLayerOf 2 (centralizer ((imgBar x D : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) ⊓ L) = L := by
    rw [inf_eq_right.2 hLD]
    exact le_antisymm (sSup_le fun L' hL' => hL'.1) (le_sSup hL.isPCompIn_self)
  have hDcomm : D ≤ centralizer (D : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb =>
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥D)).comm ⟨b, hb⟩ ⟨a, ha⟩)
  refine ⟨y, L, ⟨⟨hyC, hy2, hyne, hrel, fun _ => ⟨hL.isPCompIn, fun L' hL' _ =>
    hL.card_le_of_isPCompIn hL'⟩⟩, D, L, ⟨hDA, hDel, hDrank⟩,
    Or.inl ⟨⟨hyC, hy2, hyne, hDC, hDel, fun d hd => Subgroup.le_normalizer hd, ?_⟩,
      Subgroup.le_normalizer hyK, hL.pLayerOf_ne_bot, hL.isPCompIn, ?_⟩⟩⟩
  · rw [inf_eq_left.2 hDcomm]
    exact hDrank
  · rw [hLself]; exact hL.isPCompIn_self

theorem exists_adm_of_shape5 {x : G} {K A : Subgroup G}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (h5 : QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) (hA : IsSource2 x K A) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  obtain ⟨-, -, -, hcase⟩ := hA
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, -, hEel, hE4, -⟩
  · exact (not_qShape1_of_qShape5 h1 h5).elim
  · have hxK : x ∉ K := not_mem_of_center_trivial hx hK.1 (center_of_isSporadic h5)
    obtain ⟨eK⟩ := hat_equiv_imgBar hK
    obtain ⟨e5⟩ := h5
    exact exists_adm_of_split hx hK hxK
      (SplitLike.of_equiv (eK.symm.trans (e5.trans walterJ1EquivNative.symm))) hEK hAE hEel hE4

end GLevel

end CFSG.GH74.Generic.BProg.B1.PilotS5

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem sourceExistsFor_shape5 : SourceExistsFor QShape5 := by
  intro G _ _ _hyp _noAlt x K hcirc h5
  exact PilotS5.exists_source_of_shape5 hcirc.1.1.1.1 hcirc.1.1.1.2.2 h5

theorem admissibleExistsFor_shape5 : AdmissibleExistsFor QShape5 := by
  intro G _ _ _hyp _noAlt x K hcirc h5 A hA
  exact PilotS5.exists_adm_of_shape5 hcirc.1.1.1.1 hcirc.1.1.1.2.2 h5 hA

end CFSG.GH74.Generic.BProg.B1
