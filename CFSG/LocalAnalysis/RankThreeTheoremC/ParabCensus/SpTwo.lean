module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormW
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.Permutation.SylowTwoNormalizer.Alt
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup TenThreeThree

variable {k : ℕ} {X : Fin k → Type} [∀ i, Group (X i)] [∀ i, Finite (X i)]

@[expose] noncomputable def spTwoLev (i : Fin k) : Subgroup (X i) := by
  classical
  exact if h : Nonempty (X i ≃* Equiv.Perm (Fin 6)) then
    (alternatingGroup (Fin 6)).map (Classical.choice h).symm.toMonoidHom
  else ⊤

theorem spTwoLev_eq_map_alt {i : Fin k} (h : Nonempty (X i ≃* Equiv.Perm (Fin 6))) :
    spTwoLev (X := X) i =
      (alternatingGroup (Fin 6)).map (Classical.choice h).symm.toMonoidHom := by
  rw [spTwoLev, dif_pos h]

theorem spTwoLev_eq_top {i : Fin k} (h : ¬ Nonempty (X i ≃* Equiv.Perm (Fin 6))) :
    spTwoLev (X := X) i = ⊤ := by
  rw [spTwoLev, dif_neg h]

theorem spTwoLev_normal (hX : ∀ i, IsSpTwoFactor (X i)) (i : Fin k) :
    (spTwoLev (X := X) i).Normal := by
  by_cases h : Nonempty (X i ≃* Equiv.Perm (Fin 6))
  · rw [spTwoLev_eq_map_alt h]
    exact Subgroup.Normal.map alternatingGroup.normal _ (Classical.choice h).symm.surjective
  · rw [spTwoLev_eq_top h]
    exact Subgroup.normal_top

theorem isQuasisimple_alternatingGroup_six :
    CFSG.IsQuasisimple ↥(alternatingGroup (Fin 6)) := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  refine (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr ⟨?_, ?_⟩
  · exact commutator_alternatingGroup_eq_top (by simp)
  · exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot (G := alternatingGroup (Fin 6)))).isSimpleGroup

theorem isQuasisimple_spTwoLev_of_mulEquiv {i : Fin k}
    (h : Nonempty (X i ≃* Equiv.Perm (Fin 6))) :
    CFSG.IsQuasisimple ↥(spTwoLev (X := X) i) := by
  rw [spTwoLev_eq_map_alt h]
  exact CFSG.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6))
      (Classical.choice h).symm.toMonoidHom (Classical.choice h).symm.injective).symm
    isQuasisimple_alternatingGroup_six

theorem quasisimple_or_symThree_spTwoLev {i : Fin k}
    (h : ¬ Nonempty (X i ≃* Equiv.Perm (Fin 6))) (hWB : IsWBlock (X i)) :
    CFSG.IsQuasisimple ↥(spTwoLev (X := X) i) ∨
      IsSymThreeOrSUThreeTwo ↥(spTwoLev (X := X) i) := by
  rw [spTwoLev_eq_top h]
  rcases hWB with ⟨hq, -⟩ | hs
  · left
    exact CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hq)
  · exact Or.inr (IsSymThreeOrSUThreeTwo.of_mulEquiv Subgroup.topEquiv.symm hs)

theorem normal_map_mulSingle {i : Fin k} {N : Subgroup (X i)} (hN : N.Normal) :
    (N.map (MonoidHom.mulSingle X i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_map] at hn ⊢
  obtain ⟨w, hw, rfl⟩ := hn
  refine ⟨g i * w * (g i)⁻¹, hN.conj_mem w hw (g i), ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Pi.mulSingle_eq_same]
  · simp [Pi.mulSingle_eq_of_ne hj]

@[expose] noncomputable def spTwoBlock (i : Fin k) : Subgroup (∀ j, X j) :=
  (spTwoLev (X := X) i).map (MonoidHom.mulSingle X i)

@[expose] noncomputable def spTwoProduct : Subgroup (∀ j, X j) :=
  Subgroup.pi Set.univ (spTwoLev (X := X))

theorem spTwoBlock_normal (hX : ∀ i, IsSpTwoFactor (X i)) (i : Fin k) :
    (spTwoBlock (X := X) i).Normal :=
  normal_map_mulSingle (spTwoLev_normal hX i)

theorem spTwoProduct_normal (hX : ∀ i, IsSpTwoFactor (X i)) :
    (spTwoProduct (X := X)).Normal := by
  refine ⟨fun m hm g => ?_⟩
  rw [spTwoProduct, Subgroup.mem_pi] at hm ⊢
  intro i _
  exact (spTwoLev_normal hX i).conj_mem (m i) (hm i trivial) (g i)

theorem spTwoBlock_le_wSup (hX : ∀ i, IsSpTwoFactor (X i)) (i : Fin k) :
    spTwoBlock (X := X) i ≤ wSup (∀ j, X j) := by
  by_cases h6 : Nonempty (X i ≃* Equiv.Perm (Fin 6))
  · refine le_wSup_of_normal_of_isQuasisimple (spTwoBlock_normal hX i) ?_
    exact CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
        (Pi.mulSingle_injective i)).symm
      (isQuasisimple_spTwoLev_of_mulEquiv h6)
  · rcases hX i with hs | ⟨hWB, -, -⟩ | h6'
    · haveI : Subsingleton (X i) := hs
      rw [spTwoBlock, spTwoLev_eq_top h6,
        Subgroup.eq_bot_of_subsingleton (⊤ : Subgroup (X i)), Subgroup.map_bot]
      exact bot_le
    · have hB := spTwoBlock_normal hX i
      rcases quasisimple_or_symThree_spTwoLev h6 hWB with hq | hs3
      · refine le_wSup_of_normal_of_isQuasisimple hB ?_
        exact CFSG.IsQuasisimple.of_mulEquiv
          (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
            (Pi.mulSingle_injective i)).symm hq
      · haveI := hB
        refine le_wSup_of_subnormal_of_symThree
          (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)) ?_
        exact IsSymThreeOrSUThreeTwo.of_mulEquiv
          (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
            (Pi.mulSingle_injective i)) hs3
    · exact absurd h6' h6

theorem spTwoProduct_le_wSup (hX : ∀ i, IsSpTwoFactor (X i)) :
    spTwoProduct (X := X) ≤ wSup (∀ j, X j) := by
  intro x hx
  rw [← Finset.noncommProd_mulSingle x]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  exact spTwoBlock_le_wSup hX i ⟨x i, (Subgroup.mem_pi _).mp hx i trivial, rfl⟩

theorem relIndex_inf_spTwoProduct_odd (hX : ∀ i, IsSpTwoFactor (X i))
    {T : Subgroup (∀ j, X j)} (hTW : T ≤ wSup (∀ j, X j))
    (hTi : ¬ 2 ∣ T.relIndex (wSup (∀ j, X j))) :
    ¬ 2 ∣ (T ⊓ spTwoProduct (X := X)).relIndex (spTwoProduct (X := X)) := by
  classical
  set M := spTwoProduct (X := X) with hM
  have hMW : M ≤ wSup (∀ j, X j) := spTwoProduct_le_wSup hX
  haveI : M.Normal := spTwoProduct_normal hX
  have hcard : Nat.card ↥(T ⊔ M : Subgroup (∀ j, X j)) * Nat.card ↥(T ⊓ M) =
      Nat.card ↥T * Nat.card ↥M := by
    have h1 := Subgroup.relIndex_mul_card (H := M) (K := T)
    have h2 := Subgroup.relIndex_mul_card (H := M) (K := M ⊔ T)
    rw [Subgroup.relIndex_sup_left T M, inf_eq_left.mpr le_sup_left] at h2
    have h2' : Nat.card ↥(T ⊔ M) = M.relIndex T * Nat.card ↥M := by
      rw [sup_comm]; exact h2.symm
    calc Nat.card ↥(T ⊔ M) * Nat.card ↥(T ⊓ M)
        = (M.relIndex T * Nat.card ↥M) * Nat.card ↥(T ⊓ M) := by rw [h2']
      _ = Nat.card ↥M * (M.relIndex T * Nat.card ↥(M ⊓ T)) := by
            rw [inf_comm]; ring
      _ = Nat.card ↥M * Nat.card ↥T := by rw [h1]
      _ = Nat.card ↥T * Nat.card ↥M := by ring
  have heq : (T ⊓ M).relIndex M = T.relIndex (T ⊔ M) := by
    have hS1 := Subgroup.relIndex_mul_card (H := T ⊓ M) (K := M)
    rw [inf_eq_left.mpr inf_le_right] at hS1
    have hT1 := Subgroup.relIndex_mul_card (H := T) (K := T ⊔ M)
    rw [inf_eq_left.mpr le_sup_left] at hT1
    have hc : (T ⊓ M).relIndex M * (Nat.card ↥T * Nat.card ↥(T ⊓ M)) =
        T.relIndex (T ⊔ M) * (Nat.card ↥T * Nat.card ↥(T ⊓ M)) := by
      calc (T ⊓ M).relIndex M * (Nat.card ↥T * Nat.card ↥(T ⊓ M))
          = Nat.card ↥T * ((T ⊓ M).relIndex M * Nat.card ↥(T ⊓ M)) := by ring
        _ = Nat.card ↥T * Nat.card ↥M := by rw [hS1]
        _ = Nat.card ↥M * Nat.card ↥T := by ring
        _ = Nat.card ↥(T ⊔ M) * Nat.card ↥(T ⊓ M) := by
              rw [Nat.mul_comm]; exact hcard.symm
        _ = (T.relIndex (T ⊔ M) * Nat.card ↥T) * Nat.card ↥(T ⊓ M) := by rw [hT1]
        _ = T.relIndex (T ⊔ M) * (Nat.card ↥T * Nat.card ↥(T ⊓ M)) := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) hc
  have hdvd : (T ⊓ M).relIndex M ∣ T.relIndex (wSup (∀ j, X j)) := by
    rw [heq]
    exact ⟨_, (Subgroup.relIndex_mul_relIndex T (T ⊔ M) (wSup (∀ j, X j))
      le_sup_left (sup_le hTW hMW)).symm⟩
  intro h2
  exact hTi (h2.trans hdvd)

theorem exists_coordinate_of_relIndex (hX : ∀ i, IsSpTwoFactor (X i))
    {T : Subgroup (∀ j, X j)} (hT : IsPGroup 2 T)
    (hTW : T ≤ wSup (∀ j, X j))
    (hTi : ¬ 2 ∣ T.relIndex (wSup (∀ j, X j)))
    {x : ∀ j, X j} (hxT : x ∈ normalizer (T : Set (∀ j, X j))) (i : Fin k) :
    ∃ U : Subgroup (X i), IsPGroup 2 U ∧ U ≤ spTwoLev (X := X) i ∧
      ¬ 2 ∣ U.relIndex (spTwoLev (X := X) i) ∧
      x i ∈ normalizer (U : Set (X i)) := by
  classical
  set M := spTwoProduct (X := X) with hM
  set S : Subgroup (∀ j, X j) := T ⊓ M with hS
  have hS2 : IsPGroup 2 S := hT.to_le inf_le_left
  have hSM : S ≤ M := inf_le_right
  have hSodd : ¬ 2 ∣ S.relIndex M := by
    rw [hS]
    exact relIndex_inf_spTwoProduct_odd hX hTW hTi
  haveI : M.Normal := spTwoProduct_normal hX
  have hxM : x ∈ normalizer (M : Set (∀ j, X j)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hxS : x ∈ normalizer (S : Set (∀ j, X j)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxT s).mp hs.1,
        (Subgroup.mem_normalizer_iff.mp hxM s).mp hs.2⟩
    · intro hs
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxT s).mpr hs.1,
        (Subgroup.mem_normalizer_iff.mp hxM s).mpr hs.2⟩
  refine ⟨S.map (Pi.evalMonoidHom X i), hS2.map _, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_pi _).mp hs.2 i trivial
  ·
    let πi : ↥M →* ↥(spTwoLev (X := X) i) :=
      { toFun := fun m => ⟨m.1 i, (Subgroup.mem_pi _).mp m.2 i trivial⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hπi : Function.Surjective πi := by
      intro w
      refine ⟨⟨Pi.mulSingle i w.1, ?_⟩, ?_⟩
      · rw [hM, spTwoProduct, Subgroup.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using w.2
        · simp [Pi.mulSingle_eq_of_ne hj]
      · ext
        simp [πi, Pi.mulSingle_eq_same]
    have hmap : (S.subgroupOf M).map πi =
        (S.map (Pi.evalMonoidHom X i)).subgroupOf (spTwoLev (X := X) i) := by
      ext w
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨s, hs, hsw⟩
        rw [Subgroup.mem_subgroupOf] at hs ⊢
        exact ⟨s.1, hs, by rw [← hsw]; rfl⟩
      · intro hw
        rw [Subgroup.mem_subgroupOf] at hw
        obtain ⟨s, hsS, hsi⟩ := hw
        refine ⟨⟨s, hSM hsS⟩, ?_, Subtype.ext hsi⟩
        rwa [Subgroup.mem_subgroupOf]
    have hdiv := Subgroup.index_map_dvd (H := S.subgroupOf M) hπi
    rw [hmap] at hdiv
    intro h2
    exact hSodd (h2.trans hdiv)
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxS s).mp hs, rfl⟩
    · rintro ⟨s, hs, hconj⟩
      refine ⟨x⁻¹ * s * x, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxS) s).mp hs
      · have hconj' : s i = x i * h * (x i)⁻¹ := hconj
        show (x⁻¹ * s * x) i = h
        simp only [Pi.mul_apply, Pi.inv_apply, hconj']
        group

theorem eq_one_of_mem_normalizer_spTwoLev (hX : ∀ i, IsSpTwoFactor (X i)) {i : Fin k}
    {x : X i} (hx : Odd (orderOf x)) {U : Subgroup (X i)}
    (hU : IsPGroup 2 U) (hUW : U ≤ spTwoLev (X := X) i)
    (hUi : ¬ 2 ∣ U.relIndex (spTwoLev (X := X) i))
    (hxU : x ∈ normalizer (U : Set (X i))) : x = 1 := by
  classical
  by_cases h6 : Nonempty (X i ≃* Equiv.Perm (Fin 6))
  ·
    set e : X i ≃* Equiv.Perm (Fin 6) := Classical.choice h6 with he
    have hsp : spTwoLev (X := X) i =
        (alternatingGroup (Fin 6)).map e.symm.toMonoidHom := by
      rw [spTwoLev_eq_map_alt h6]
    have hmap : (spTwoLev (X := X) i).map e.toMonoidHom = alternatingGroup (Fin 6) := by
      rw [hsp, Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom =
          MonoidHom.id (Equiv.Perm (Fin 6)) := by
        ext y; simp
      rw [hcomp, Subgroup.map_id]
    have hRA : U.map e.toMonoidHom ≤ alternatingGroup (Fin 6) := by
      calc U.map e.toMonoidHom ≤ (spTwoLev (X := X) i).map e.toMonoidHom :=
            Subgroup.map_mono hUW
        _ = alternatingGroup (Fin 6) := hmap
    have hR : IsPGroup 2 (U.map e.toMonoidHom) := hU.map e.toMonoidHom
    have hRi : ¬ 2 ∣ (U.map e.toMonoidHom).relIndex (alternatingGroup (Fin 6)) := by
      have hrel := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) U
        (spTwoLev (X := X) i) e.injective
      rw [hmap] at hrel
      rw [hrel]
      exact hUi
    have hσ : Odd (orderOf (e x)) := hx.of_dvd_nat (orderOf_map_dvd e.toMonoidHom x)
    have hσR : e x ∈ normalizer ((U.map e.toMonoidHom : Subgroup (Equiv.Perm (Fin 6))) :
        Set (Equiv.Perm (Fin 6))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨x * u * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxU u).mp hu, by simp⟩
      · rintro ⟨u, hu, hconj⟩
        refine ⟨x⁻¹ * u * x, ?_, ?_⟩
        · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxU) u).mp hu
        · have hconj' : e u = e x * h * (e x)⁻¹ := hconj
          calc e (x⁻¹ * u * x) = (e x)⁻¹ * e u * e x := by simp
            _ = h := by rw [hconj']; group
    have hx1 : e x = 1 :=
      CFSG.Permutation.SylowTwoNormalizer.eq_one_of_mem_normalizer_of_le_alternatingGroup
        (Ω := Fin 6) (by simp) hRA hR hRi hσ hσR
    exact e.injective (hx1.trans (map_one e).symm)
  ·
    rw [spTwoLev_eq_top h6] at hUW hUi
    rcases hX i with hs | ⟨-, -, hsyl⟩ | h6'
    · haveI : Subsingleton (X i) := hs
      exact Subsingleton.elim x 1
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hUidx : ¬ 2 ∣ U.index := by
        rwa [Subgroup.relIndex_top_right] at hUi
      let S : Sylow 2 (X i) := hU.toSylow hUidx
      have hScoe : (S : Subgroup (X i)) = U := rfl
      have hxS : x ∈ (S : Subgroup (X i)) := by
        have hxN : x ∈ normalizer ((S : Subgroup (X i)) : Set (X i)) := by
          rw [hScoe]; exact hxU
        rw [hsyl S] at hxN
        exact hxN
      have hxU' : x ∈ U := hScoe ▸ hxS
      obtain ⟨n, hn⟩ := hU ⟨x, hxU'⟩
      have hpow : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
      rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd
      obtain ⟨m, -, hm⟩ := hdvd
      have hm0 : m = 0 := by
        by_contra hm0
        have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
        exact (Odd.not_two_dvd_nat hx) (hm ▸ h2)
      have ho1 : orderOf x = 1 := by rw [hm, hm0, pow_zero]
      exact orderOf_eq_one_iff.mp ho1
    · exact absurd h6' h6

theorem eq_one_of_mem_normalizer_pi (hX : ∀ i, IsSpTwoFactor (X i))
    {x : ∀ i, X i} (hx : Odd (orderOf x)) {T : Subgroup (∀ i, X i)}
    (hT : IsPGroup 2 T) (hTW : T ≤ wSup (∀ i, X i))
    (hTi : ¬ 2 ∣ T.relIndex (wSup (∀ i, X i)))
    (hxT : x ∈ normalizer (T : Set (∀ i, X i))) : x = 1 := by
  funext i
  obtain ⟨U, hU, hUW, hUi, hxU⟩ := exists_coordinate_of_relIndex hX hT hTW hTi hxT i
  exact eq_one_of_mem_normalizer_spTwoLev hX
    (hx.of_dvd_nat (orderOf_map_dvd (Pi.evalMonoidHom X i) x)) hU hUW hUi hxU

theorem eq_one_of_centralizes_spTwoLev (hX : ∀ i, IsSpTwoFactor (X i)) (i : Fin k)
    {c : X i} (hc : ∀ w ∈ spTwoLev (X := X) i, w * c = c * w) : c = 1 := by
  classical
  by_cases h6 : Nonempty (X i ≃* Equiv.Perm (Fin 6))
  · set e : X i ≃* Equiv.Perm (Fin 6) := Classical.choice h6 with he
    have hsp : spTwoLev (X := X) i =
        (alternatingGroup (Fin 6)).map e.symm.toMonoidHom := by
      rw [spTwoLev_eq_map_alt h6]
    have hc' : ∀ a ∈ alternatingGroup (Fin 6), a * e c = e c * a := by
      intro a ha
      have ha' : e.symm a ∈ spTwoLev (X := X) i := by
        rw [hsp]; exact Subgroup.mem_map_of_mem _ ha
      have hcomm := hc (e.symm a) ha'
      calc a * e c = e (e.symm a) * e c := by simp
        _ = e (e.symm a * c) := by simp
        _ = e (c * e.symm a) := by rw [hcomm]
        _ = e c * a := by simp
    have hconj : MulAut.conjNormal (H := alternatingGroup (Fin 6)) (e c) = 1 := by
      ext a
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hc' a a.2]
      group
    have hinj :=
      CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
    have h1 : e c = 1 :=
      hinj (hconj.trans (map_one (MulAut.conjNormal (H := alternatingGroup (Fin 6)))).symm)
    exact e.injective (h1.trans (map_one e).symm)
  · rw [spTwoLev_eq_top h6] at hc
    rcases hX i with hs | ⟨-, hcenter, -⟩ | h6'
    · haveI : Subsingleton (X i) := hs
      exact Subsingleton.elim c 1
    · have hcen : c ∈ Subgroup.center (X i) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact hc g (Subgroup.mem_top g)
      rw [hcenter] at hcen
      exact Subgroup.mem_bot.mp hcen
    · exact absurd h6' h6

theorem centralizer_wSup_pi_eq_bot (hX : ∀ i, IsSpTwoFactor (X i)) :
    centralizer (wSup (∀ i, X i) : Set (∀ i, X i)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro c hc
  rw [Subgroup.mem_bot]
  funext i
  refine eq_one_of_centralizes_spTwoLev hX i ?_
  intro w hw
  have hmem : Pi.mulSingle i w ∈ wSup (∀ j, X j) :=
    spTwoBlock_le_wSup hX i ⟨w, hw, rfl⟩
  have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (Pi.mulSingle i w) hmem
  simpa using congrFun hcomm i

theorem exists_wGen_pi (hX : ∀ i, IsSpTwoFactor (X i))
    (h2 : 2 ∣ Nat.card (∀ i, X i)) :
    ∃ T : Subgroup (∀ i, X i), IsSubnormal T ⊤ ∧
      (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T) := by
  classical
  have h2prod : 2 ∣ ∏ i : Fin k, Nat.card (X i) := by
    rwa [← Nat.card_pi]
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp Nat.prime_two)
    (fun i => Nat.card (X i))).mp h2prod
  have hcard1 : Nat.card (X i) ≠ 1 := by
    intro h
    exact Nat.Prime.not_dvd_one Nat.prime_two (h ▸ hi)
  have hns : ¬ Subsingleton (X i) := by
    intro hs
    exact hcard1 (Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩)
  have hB : (spTwoBlock (X := X) i).Normal := spTwoBlock_normal hX i
  haveI : (spTwoBlock (X := X) i).Normal := hB
  have hsub : IsSubnormal (spTwoBlock (X := X) i) ⊤ :=
    CFSG.Open.IsSubnormal.step le_top (Subgroup.normal_subgroupOf)
      (CFSG.Open.IsSubnormal.refl ⊤)
  rcases hX i with hs | ⟨hWB, -, -⟩ | h6
  · exact absurd hs hns
  · by_cases h6 : Nonempty (X i ≃* Equiv.Perm (Fin 6))
    · refine ⟨spTwoBlock (X := X) i, hsub, Or.inl ⟨le_top, hsub, ?_⟩⟩
      exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
          (Pi.mulSingle_injective i)).symm
        ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp
          (isQuasisimple_spTwoLev_of_mulEquiv h6))
    · rcases quasisimple_or_symThree_spTwoLev h6 hWB with hq | hs3
      · refine ⟨spTwoBlock (X := X) i, hsub, Or.inl ⟨le_top, hsub, ?_⟩⟩
        exact CFSG.Open.IsQuasisimple.of_mulEquiv
          (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
            (Pi.mulSingle_injective i)).symm
          ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hq)
      · refine ⟨spTwoBlock (X := X) i, hsub, Or.inr ?_⟩
        exact IsSymThreeOrSUThreeTwo.of_mulEquiv
          (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
            (Pi.mulSingle_injective i)) hs3
  · refine ⟨spTwoBlock (X := X) i, hsub, Or.inl ⟨le_top, hsub, ?_⟩⟩
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (spTwoLev (X := X) i) (MonoidHom.mulSingle X i)
        (Pi.mulSingle_injective i)).symm
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp
        (isQuasisimple_spTwoLev_of_mulEquiv h6))

variable {R : Type} [Group R] [Finite R]

theorem IsSpTwoLeviProduct.eq_one_of_mem_normalizer (h : IsSpTwoLeviProduct R)
    {x : R ⧸ CFSG.pCore 2 R} (hx : Odd (orderOf x)) {T : Subgroup (R ⧸ CFSG.pCore 2 R)}
    (hT : IsPGroup 2 T) (hTW : T ≤ wSup (R ⧸ CFSG.pCore 2 R))
    (hTi : ¬ 2 ∣ T.relIndex (wSup (R ⧸ CFSG.pCore 2 R)))
    (hxT : x ∈ normalizer (T : Set (R ⧸ CFSG.pCore 2 R))) : x = 1 := by
  classical
  obtain ⟨k, X, hgrp, hfin, ⟨e⟩, hX⟩ := h
  letI : ∀ i, Group (X i) := hgrp
  letI : ∀ i, Finite (X i) := hfin
  have hT' : IsPGroup 2 (T.map e.toMonoidHom) := hT.map e.toMonoidHom
  have hT'W : T.map e.toMonoidHom ≤ wSup (∀ i, X i) := by
    rw [← map_wSup_eq e]
    exact Subgroup.map_mono hTW
  have hTi' : ¬ 2 ∣ (T.map e.toMonoidHom).relIndex (wSup (∀ i, X i)) := by
    have hrel := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) T
      (wSup (R ⧸ CFSG.pCore 2 R)) e.injective
    rw [map_wSup_eq e] at hrel
    rw [hrel]
    exact hTi
  have hx' : Odd (orderOf (e x)) := hx.of_dvd_nat (orderOf_map_dvd e.toMonoidHom x)
  have hxT' : e x ∈ normalizer ((T.map e.toMonoidHom : Subgroup (∀ i, X i)) :
      Set (∀ i, X i)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxT t).mp ht, by simp⟩
    · rintro ⟨t, ht, hconj⟩
      refine ⟨x⁻¹ * t * x, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxT) t).mp ht
      · have hconj' : e t = e x * y * (e x)⁻¹ := hconj
        calc e (x⁻¹ * t * x) = (e x)⁻¹ * e t * e x := by simp
          _ = y := by rw [hconj']; group
  have hx1 : e x = 1 := eq_one_of_mem_normalizer_pi hX hx' hT' hT'W hTi' hxT'
  exact e.injective (hx1.trans (map_one e).symm)

theorem IsSpTwoLeviProduct.centralizer_wSup_eq_bot (h : IsSpTwoLeviProduct R) :
    centralizer (wSup (R ⧸ CFSG.pCore 2 R) : Set (R ⧸ CFSG.pCore 2 R)) = ⊥ := by
  classical
  obtain ⟨k, X, hgrp, hfin, ⟨e⟩, hX⟩ := h
  letI : ∀ i, Group (X i) := hgrp
  letI : ∀ i, Finite (X i) := hfin
  refine le_antisymm ?_ bot_le
  intro c hc
  rw [Subgroup.mem_bot]
  have hc' : e c ∈ centralizer (wSup (∀ i, X i) : Set (∀ i, X i)) := by
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [← map_wSup_eq e] at hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    simpa using congrArg e (hc t ht)
  have hc1 : e c = 1 := by
    have hmem := hc'
    rw [centralizer_wSup_pi_eq_bot hX] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact e.injective (hc1.trans (map_one e).symm)

theorem IsSpTwoLeviProduct.exists_wGen (h : IsSpTwoLeviProduct R)
    (h2 : 2 ∣ Nat.card (R ⧸ CFSG.pCore 2 R)) :
    ∃ T : Subgroup (R ⧸ CFSG.pCore 2 R), IsSubnormal T ⊤ ∧
      (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T) := by
  classical
  obtain ⟨k, X, hgrp, hfin, ⟨e⟩, hX⟩ := h
  letI : ∀ i, Group (X i) := hgrp
  letI : ∀ i, Finite (X i) := hfin
  have h2' : 2 ∣ Nat.card (∀ i, X i) := by
    rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨T, hsub, hshape⟩ := exists_wGen_pi hX h2'
  exact ⟨T.map e.symm.toMonoidHom, map_isSubnormal_and_shape e.symm hsub hshape⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
