module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a2
public import CFSG.LocalAnalysis.GLTheoremB.A7Centralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a4

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped commutatorElement

@[expose] def IsOddCenterAltSeven (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Odd (Nat.card (Subgroup.center X)) ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 7))

section Commutators

variable {X : Type*} [Group X]

theorem commutatorElement_mul_central_left {z : X} (hz : z ∈ Subgroup.center X) (w h : X) :
    ⁅w * z, h⁆ = ⁅w, h⁆ := by
  have hzc : ∀ g : X, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  rw [commutatorElement_def, commutatorElement_def]
  calc w * z * h * (w * z)⁻¹ * h⁻¹ = w * (z * h) * z⁻¹ * w⁻¹ * h⁻¹ := by group
    _ = w * (h * z) * z⁻¹ * w⁻¹ * h⁻¹ := by rw [← hzc h]
    _ = w * h * w⁻¹ * h⁻¹ := by group

theorem commutatorElement_mul_central_right {z : X} (hz : z ∈ Subgroup.center X) (w h : X) :
    ⁅h, w * z⁆ = ⁅h, w⁆ := by
  have hzc : ∀ g : X, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  rw [commutatorElement_def, commutatorElement_def]
  calc h * (w * z) * h⁻¹ * (w * z)⁻¹ = h * w * (z * h⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = h * w * (h⁻¹ * z) * z⁻¹ * w⁻¹ := by rw [← hzc h⁻¹]
    _ = h * w * h⁻¹ * w⁻¹ := by group

end Commutators

section NormalGeneration

theorem normalClosure_eq_top_of_isOddCenterAltSeven {J : Type} [Group J] [Finite J]
    (hperf : commutator J = ⊤) (hX : IsOddCenterAltSeven (J ⧸ CFSG.pCore 2 J))
    {V : Subgroup J} (hV : IsPGroup 2 ↥V) (hVO : ¬ V ≤ CFSG.pCore 2 J) :
    Subgroup.normalClosure (V : Set J) = ⊤ := by
  classical
  obtain ⟨hXperf, hZodd, ⟨e⟩⟩ := hX
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := S7.isSimple_Alt7
  let π : J →* (J ⧸ CFSG.pCore 2 J) := QuotientGroup.mk' (CFSG.pCore 2 J)
  let ψ : (J ⧸ CFSG.pCore 2 J) →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (J ⧸ CFSG.pCore 2 J)))
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψ : ∀ x : J ⧸ CFSG.pCore 2 J, ψ x = 1 ↔ x ∈ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
    intro x
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (Subgroup.center (J ⧸ CFSG.pCore 2 J)) x : _) = 1 :=
        e.injective (by simpa [ψ] using h)
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro h
      simp [ψ, (QuotientGroup.eq_one_iff x).2 h]
  set W : Subgroup J := Subgroup.normalClosure (V : Set J) with hWdef
  haveI : W.Normal := Subgroup.normalClosure_normal
  set W' : Subgroup (J ⧸ CFSG.pCore 2 J) := W.map π with hW'def
  have hW'n : W'.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hVW : ∀ v ∈ V, π v ∈ W' := fun v hv =>
    Subgroup.mem_map_of_mem π (Subgroup.subset_normalClosure hv)
  have hS : W'.map ψ ≠ ⊥ := by
    intro hbot
    have hle : V.map π ≤ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
      rintro _ ⟨v, hv, rfl⟩
      have h1 : ψ (π v) ∈ W'.map ψ := Subgroup.mem_map_of_mem ψ (hVW v hv)
      rw [hbot, Subgroup.mem_bot] at h1
      exact (hψ _).1 h1
    have hV0 : V.map π = ⊥ := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hV.map π)
      have hdvd : Nat.card (V.map π) ∣ Nat.card (Subgroup.center (J ⧸ CFSG.pCore 2 J)) :=
        Subgroup.card_dvd_of_le hle
      rw [hn] at hdvd
      have hodd : Odd (2 ^ n) := Odd.of_dvd_nat hZodd hdvd
      have hn0 : n = 0 := by
        by_contra hn0
        have : Even (2 ^ n) := (Nat.even_pow).2 ⟨even_two, hn0⟩
        exact (Nat.not_even_iff_odd.2 hodd) this
      rw [hn0, pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq _ hn
    apply hVO
    intro v hv
    have h1 : π v ∈ V.map π := Subgroup.mem_map_of_mem π hv
    rw [hV0, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff v).1 h1
  haveI hSn : (W'.map ψ).Normal := Subgroup.Normal.map hW'n ψ hψsurj
  have hSt : W'.map ψ = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (W'.map ψ)).resolve_left hS
  have hdec : ∀ g : J ⧸ CFSG.pCore 2 J, ∃ w ∈ W', ∃ z ∈ Subgroup.center (J ⧸ CFSG.pCore 2 J),
      g = w * z := by
    intro g
    have hg : ψ g ∈ W'.map ψ := by rw [hSt]; exact Subgroup.mem_top _
    obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 hg
    refine ⟨w, hw, w⁻¹ * g, ?_, by group⟩
    rw [← hψ]
    simp [map_mul, map_inv, hwg]
  have hcomm : commutator (J ⧸ CFSG.pCore 2 J) ≤ W' := by
    show ⁅(⊤ : Subgroup (J ⧸ CFSG.pCore 2 J)), ⊤⁆ ≤ W'
    rw [Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨w, hw, z, hz, hgz⟩ := hdec g
    obtain ⟨w', hw', z', hz', hhz⟩ := hdec h
    rw [hgz, hhz, commutatorElement_mul_central_right hz', commutatorElement_mul_central_left hz,
      commutatorElement_def]
    exact W'.mul_mem (hW'n.conj_mem w' hw' w) (W'.inv_mem hw')
  have hW'top : W' = ⊤ := top_le_iff.1 (hXperf.symm.le.trans hcomm)
  have hWO : ∀ j : J, ∃ w ∈ W, ∃ o ∈ CFSG.pCore 2 J, j = w * o := by
    intro j
    have hj : π j ∈ W' := by rw [hW'top]; exact Subgroup.mem_top _
    obtain ⟨w, hw, hwj⟩ := Subgroup.mem_map.1 hj
    refine ⟨w, hw, w⁻¹ * j, ?_, by group⟩
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 J) (w⁻¹ * j) = 1 := by
      rw [map_mul, map_inv]
      show (π w)⁻¹ * π j = 1
      rw [hwj, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (w⁻¹ * j)).1 h1
  haveI : Group.IsPerfect J := Group.isPerfect_def.2 hperf
  let ρ : J →* (J ⧸ W) := QuotientGroup.mk' W
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective W
  haveI : Group.IsPerfect (J ⧸ W) := Group.IsPerfect.ofSurjective hρsurj
  have hOmap : (CFSG.pCore 2 J).map ρ = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨j, rfl⟩ := hρsurj q
    obtain ⟨w, hw, o, ho, rfl⟩ := hWO j
    have hw1 : ρ w = 1 := (QuotientGroup.eq_one_iff w).2 hw
    refine Subgroup.mem_map.2 ⟨o, ho, ?_⟩
    rw [map_mul, hw1, one_mul]
  have hQ2 : IsPGroup 2 (J ⧸ W) := by
    intro q
    have hq : q ∈ (CFSG.pCore 2 J).map ρ := by rw [hOmap]; exact Subgroup.mem_top _
    obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)) ⟨o, ho⟩
    refine ⟨k, ?_⟩
    have hk' : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow, hk', map_one]
  haveI : Subsingleton (J ⧸ W) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    haveI : Group.IsNilpotent (J ⧸ W) := hQ2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (G := J ⧸ W) inferInstance
  have hWtop : W = ⊤ := by
    rw [eq_top_iff]
    intro j _
    exact (QuotientGroup.eq_one_iff j).1 (Subsingleton.elim (ρ j) 1)
  exact hWtop

end NormalGeneration

theorem le_iSup_conj_of_isOddCenterAltSeven {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hX : IsOddCenterAltSeven (↥J ⧸ CFSG.pCore 2 ↥J))
    {V : Subgroup G} (hVJ : V ≤ J) (hV : IsPGroup 2 ↥V)
    (hVO : ¬ V ≤ CFSG.Open.pCoreOf 2 J) :
    J ≤ ⨆ g ∈ J, GLBConj g V := by
  classical
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJ
  have hperf : commutator ↥J = ⊤ := Group.isPerfect_def.1 inferInstance
  set V' : Subgroup ↥J := V.subgroupOf J with hV'def
  have hV' : IsPGroup 2 ↥V' := by
    intro g
    obtain ⟨k, hk⟩ := hV ⟨(g.1 : G), Subgroup.mem_subgroupOf.1 g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hV'O : ¬ V' ≤ CFSG.pCore 2 ↥J := by
    intro h
    apply hVO
    intro v hv
    have hvJ : (⟨v, hVJ hv⟩ : ↥J) ∈ V' := Subgroup.mem_subgroupOf.2 hv
    exact Subgroup.mem_map.2 ⟨⟨v, hVJ hv⟩, h hvJ, rfl⟩
  have hN := normalClosure_eq_top_of_isOddCenterAltSeven hperf hX hV' hV'O
  set K : Subgroup G := ⨆ g : ↥J, GLBConj (g : G) V with hKdef
  have hK_mem : ∀ g : ↥J, GLBConj (g : G) V ≤ K := fun g =>
    le_iSup (fun g : ↥J => GLBConj (g : G) V) g
  have hVK : V ≤ K := by
    intro x hx
    have h1 : x ∈ GLBConj ((1 : ↥J) : G) V :=
      Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
    exact hK_mem 1 h1
  have hconj : ∀ x ∈ K, ∀ g : ↥J, (g : G) * x * (g : G)⁻¹ ∈ K := by
    intro x hx
    refine Subgroup.iSup_induction (fun h : ↥J => GLBConj (h : G) V)
      (C := fun x => ∀ g : ↥J, (g : G) * x * (g : G)⁻¹ ∈ K) hx ?_ ?_ ?_
    · intro h y hy g
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
      apply hK_mem (h * g⁻¹)
      refine Subgroup.mem_map.2 ⟨v, hv, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro g
      simp
    · intro x y hx hy g
      have e : (g : G) * (x * y) * (g : G)⁻¹ =
          ((g : G) * x * (g : G)⁻¹) * ((g : G) * y * (g : G)⁻¹) := by group
      rw [e]
      exact K.mul_mem (hx g) (hy g)
  haveI hKJ : (K.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj _ hn g⟩
  have hle : Subgroup.normalClosure (V' : Set ↥J) ≤ K.subgroupOf J := by
    apply Subgroup.normalClosure_le_normal
    intro v hv
    have hv' : (v : G) ∈ V := Subgroup.mem_subgroupOf.1 hv
    exact Subgroup.mem_subgroupOf.2 (hVK hv')
  have hJK : J ≤ K := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥J) ∈ Subgroup.normalClosure (V' : Set ↥J) := by
      rw [hN]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 (hle h1)
  exact hJK.trans (iSup_le fun g => le_iSup₂_of_le (g : G) g.2 le_rfl)

theorem pieceIII_of_isOddCenterAltSeven {G : Type} [Group G] [Finite G] {p : ℕ} {M A : Subgroup G}
    {a x : G} {V J : Subgroup G}
    (hV : V ≤ Tof p M a ⊓ Subgroup.centralizer (A : Set G)) (hVJ : V ≤ J)
    (hJ : J ≤ alphaOf p M ⊓ Cg x) (hperf : ⁅J, J⁆ = J)
    (hX : IsOddCenterAltSeven (↥J ⧸ CFSG.pCore 2 ↥J)) (hVO : ¬ V ≤ CFSG.Open.pCoreOf 2 J) :
    Sec12a2.PieceIII p M A a x V J := by
  have hT2 : IsPGroup 2 ↥(Tof p M a) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (alphaOf p M ⊓ Cg a)
  have hV2 : IsPGroup 2 ↥V := hT2.to_le (hV.trans inf_le_left)
  refine ⟨hV, hVJ, hJ, hperf, ?_⟩
  exact (le_iSup_conj_of_isOddCenterAltSeven hperf hX hVJ hV2 hVO).trans
    (iSup₂_le fun g hg => le_iSup₂_of_le g (hJ hg) le_rfl)

theorem exists_ne_one_mem_of_index_le {G : Type} [Group G] [Finite G] {A F D : Subgroup G}
    (hFA : F ≤ A) (hDA : D ≤ A) (hF : 4 ≤ Nat.card F) (hA : Nat.card A ≤ 3 * Nat.card D) :
    ∃ x : G, x ∈ F ∧ x ∈ D ∧ x ≠ 1 := by
  classical
  have hF'c : Nat.card (F.subgroupOf A) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv
  have hD'c : Nat.card (D.subgroupOf A) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  have h1 := Subgroup.card_mul_index (F.subgroupOf A)
  have h2 := Subgroup.card_mul_index (F.subgroupOf A ⊓ D.subgroupOf A)
  have h3 := Subgroup.index_inf_le (H := F.subgroupOf A) (K := D.subgroupOf A)
  have h4 := Subgroup.card_mul_index (D.subgroupOf A)
  have hfi : (F.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdpos : 0 < Nat.card (D.subgroupOf A) := Nat.card_pos
  have hdi : (D.subgroupOf A).index ≤ 3 := by
    have h5 : Nat.card (D.subgroupOf A) * (D.subgroupOf A).index ≤ Nat.card (D.subgroupOf A) * 3 := by
      rw [h4, hD'c]
      omega
    exact Nat.le_of_mul_le_mul_left h5 hdpos
  have key1 : Nat.card (F.subgroupOf A) * (F.subgroupOf A).index ≤
      Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) * ((F.subgroupOf A).index * (D.subgroupOf A).index) := by
    rw [h1, ← h2]
    exact Nat.mul_le_mul_left _ h3
  have key2 : Nat.card (F.subgroupOf A) ≤
      Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) * (D.subgroupOf A).index := by
    have hfpos : 0 < (F.subgroupOf A).index := Nat.pos_of_ne_zero hfi
    have : Nat.card (F.subgroupOf A) * (F.subgroupOf A).index ≤
        (Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) * (D.subgroupOf A).index) *
          (F.subgroupOf A).index := by
      calc Nat.card (F.subgroupOf A) * (F.subgroupOf A).index
          ≤ Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) * ((F.subgroupOf A).index * (D.subgroupOf A).index) :=
            key1
        _ = (Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) * (D.subgroupOf A).index) *
            (F.subgroupOf A).index := by ring
    exact Nat.le_of_mul_le_mul_right this hfpos
  have hc : 2 ≤ Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) := by
    by_contra hcon
    push_neg at hcon
    have h6 : Nat.card ↥(F.subgroupOf A ⊓ D.subgroupOf A) * (D.subgroupOf A).index ≤ 1 * 3 :=
      Nat.mul_le_mul (by omega) hdi
    omega
  have hne : F.subgroupOf A ⊓ D.subgroupOf A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hc
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  refine ⟨((x : A) : G), ?_, ?_, ?_⟩
  · have := (Subgroup.mem_inf.1 x.2).1
    exact Subgroup.mem_subgroupOf.1 this
  · have := (Subgroup.mem_inf.1 x.2).2
    exact Subgroup.mem_subgroupOf.1 this
  · intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h

@[expose] def BlockCoverIII : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {F : Subgroup G} (_hF : IsEkIn p 2 A F),
    ¬ Tof p M a ≤ CFSG.Open.pCoreOf 2 M →
      ∃ (ι : Type) (D V J : ι → Subgroup G),
        (∀ i, D i ≤ A ∧ Nat.card A ≤ 3 * Nat.card (D i)) ∧
        (∀ i, V i ≤ Tof p M a ⊓ Subgroup.centralizer (A : Set G)) ∧
        (∀ i, V i ≤ J i ∧ J i ≤ alphaOf p M ⊓ Subgroup.centralizer (D i : Set G) ∧
          ⁅J i, J i⁆ = J i) ∧
        (∀ i, IsOddCenterAltSeven (↥(J i) ⧸ CFSG.pCore 2 ↥(J i))) ∧
        (∀ i, ¬ V i ≤ CFSG.Open.pCoreOf 2 (J i)) ∧
        Tof p M a ⊓ Subgroup.centralizer (A : Set G) ≤
          (Tof p M a ⊓ Subgroup.centralizer (A : Set G) ⊓ CFSG.Open.pCoreOf 2 M) ⊔ ⨆ i, V i

theorem blockIII_of_inputs (hC : BlockCoverIII) : Sec12a2.BlockIII := by
  unfold Sec12a2.BlockIII
  intro G _ _ _ p _ M _ A a h F hF hT
  obtain ⟨ι, D, V, J, hD, hV, hVJ, hX, hnot, hcov⟩ := hC h hF hT
  have hp : p = 3 := (Sec12a.caseB_p3_hatSeven hT).1
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF.2.2, hp]
    norm_num
  refine hcov.trans (sup_le_sup_left (iSup_le fun i => ?_) _)
  obtain ⟨x, hxF, hxD, hx1⟩ := exists_ne_one_mem_of_index_le hF.1 (hD i).1 hF4 (hD i).2
  have hJx : J i ≤ alphaOf p M ⊓ Cg x := by
    intro j hj
    have hj' := (hVJ i).2.1 hj
    refine ⟨hj'.1, ?_⟩
    show j ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (Subgroup.mem_centralizer_iff.1 hj'.2) x hxD
  have hP : Sec12a2.PieceIII p M A a x (V i) (J i) :=
    pieceIII_of_isOddCenterAltSeven (hV i) (hVJ i).1 hJx (hVJ i).2.2 (hX i) (hnot i)
  exact le_iSup_of_le x (le_iSup_of_le hxF (le_iSup_of_le hx1
    (le_iSup_of_le (V i) (le_iSup_of_le (J i) (le_iSup_of_le hP le_rfl)))))

theorem caseB122iii_of_blockCover (hC : BlockCoverIII) : Sec12a.CaseB122iii :=
  Sec12a2.caseB122iii_of_inputs (blockIII_of_inputs hC)

theorem lemma122_iii_of_blockCover (hC : BlockCoverIII) : Lemma122_iiiStatement :=
  lemma122_iii_of_caseB (caseB122iii_of_blockCover hC)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a4
