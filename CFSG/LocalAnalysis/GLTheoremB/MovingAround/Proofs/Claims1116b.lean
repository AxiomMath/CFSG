module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.PumpDefChar
import CFSG.RankThree.PartOne.TCX.Ree.A1Layer
import CFSG.RankThree.PartOne.TCX.Ree.B2Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot)

open scoped commutatorElement

section General

noncomputable def pSimpleEquivOfBarEquiv {G : Type} [Group G] {p : ℕ} {I : Subgroup G}
    {X : Type} [Group X] (E : barOf p I ≃* X) (hZ : Subgroup.center X = ⊥) : PSimple p I ≃* X :=
  (QuotientGroup.congr (Subgroup.center (barOf p I)) (Subgroup.center X) E
    (Subgroup.map_center_eq E)).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

theorem center_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hnc : ∃ x y : X, x * y ≠ y * x) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

theorem dvd_card_barOf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X I : Subgroup G}
    (hI : GLAPComponent p X I) : p ∣ Nat.card (barOf p I) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  have hnt : Nontrivial (barOf p I) := PumpDefChar.nontrivial_barOf hp hI
  have hbot : GLAPPrimeCore p (barOf p I) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥I) p
  have hcop : Nat.Coprime p (Nat.card (barOf p I)) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have htop : (⊤ : Subgroup (barOf p I)) ≤ GLAPPrimeCore p (barOf p I) :=
    le_sSup ⟨Subgroup.normal_top, by simpa [Subgroup.card_top] using hcop⟩
  rw [hbot, top_le_iff] at htop
  exact ((Subgroup.nontrivial_iff_ne_bot _).1 (by rw [htop]; infer_instance)) rfl

theorem commutatorElement_mem_subgroupOf {T : Type} [Group T] {C N : Subgroup T}
    (hCN : ⁅C, C⁆ ≤ N) (x y : ↥C) : ⁅x, y⁆ ∈ N.subgroupOf C := by
  rw [Subgroup.mem_subgroupOf]
  refine hCN ?_
  have : ((⁅x, y⁆ : ↥C) : T) = ⁅(x : T), (y : T)⁆ := by simp [commutatorElement_def]
  rw [this]
  exact Subgroup.commutator_mem_commutator x.2 y.2

theorem normal_subgroupOf_of_commutator_le {T : Type} [Group T] {C N : Subgroup T}
    (hCN : ⁅C, C⁆ ≤ N) : (N.subgroupOf C).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by simp [commutatorElement_def]
  rw [h2]
  exact (N.subgroupOf C).mul_mem (commutatorElement_mem_subgroupOf hCN g n) hn

theorem isSolvable_quotient_of_commutator_le {T : Type} [Group T] {C N : Subgroup T}
    [(N.subgroupOf C).Normal] (hCN : ⁅C, C⁆ ≤ N) :
    Group.IsSolvable (↥C ⧸ N.subgroupOf C) := by
  refine Group.isSolvable_of_comm fun u v => ?_
  induction u using QuotientGroup.induction_on with | H x => ?_
  induction v using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
  rw [h1]
  exact commutatorElement_mem_subgroupOf hCN _ _

theorem isSolvable_of_commutator_le_bot {T : Type} [Group T] {C : Subgroup T}
    (hCN : ⁅C, C⁆ ≤ ⊥) : Group.IsSolvable ↥C := by
  refine Group.isSolvable_of_comm fun x y => ?_
  have h := commutatorElement_mem_subgroupOf hCN x y
  rw [Subgroup.bot_subgroupOf, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem fixSubgroup_one_eq_top {S : Type} [Group S] : fixSubgroup (1 : MulAut S) = ⊤ := by
  ext x
  simp [mem_fixSubgroup]

end General

section TypedLayer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.TCF
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise commutatorElement

def TypedOrBot (K : Type) [Field K] (a : ℕ) {G : Type} [Group G] (P : Subgroup G) : Prop :=
  P = ⊥ ∨ (IsSimpleGroup ↥P ∧ ¬ Group.IsSolvable ↥P ∧
    (Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥P) ∨
      Nonempty (↥(suzukiGroup a K) ≃* ↥P)))

theorem TypedOrBot.of_mulEquiv {K : Type} [Field K] {a : ℕ} {G H : Type} [Group G] [Group H]
    {P : Subgroup G} {Q : Subgroup H} (e : ↥P ≃* ↥Q) (h : TypedOrBot K a P) :
    TypedOrBot K a Q := by
  rcases h with rfl | ⟨hs, hns, hty⟩
  · left
    have : Subsingleton ↥Q := e.symm.injective.subsingleton
    exact Subgroup.eq_bot_of_subsingleton Q
  · right
    have := hs
    refine ⟨e.symm.isSimpleGroup, fun hsol => hns ?_, ?_⟩
    · exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · rcases hty with hf | hf
      · obtain ⟨f⟩ := hf
        exact Or.inl ⟨f.trans e⟩
      · obtain ⟨f⟩ := hf
        exact Or.inr ⟨f.trans e⟩

theorem TypedOrBot.of_map {K : Type} [Field K] {a : ℕ} {G H : Type} [Group G] [Group H]
    {P : Subgroup G} (f : G →* H) (hf : Function.Injective f) (h : TypedOrBot K a (P.map f)) :
    TypedOrBot K a P :=
  h.of_mulEquiv (P.equivMapOfInjective f hf).symm

section Parabolic

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

theorem typedOrBot_A1Pair [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (h : A1Pair i j) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    TypedOrBot K a (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n') := by
  haveI hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 ha hK
  have hns : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
    obtain ⟨x, y, hxy⟩ := CFSG.LieType.Ree.LargeReeInvolution.exists_SL2_mul_ne_mul (K := K)
    intro hs
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.2 hs) x y)
  obtain ⟨e⟩ := (CFSG.RankThree.PartOne.TCX.Ree.a1_level D h hK hn' hperm hstab).1
  exact Or.inr ⟨e.symm.isSimpleGroup, fun _ =>
    hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective), Or.inl ⟨e⟩⟩

theorem typedOrBot_B2 [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    TypedOrBot K a (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
      twistedFixed D.F n') := by
  obtain ⟨hfin, hnt, hsimp⟩ := suzuki_simple ha hK
  have hperf := (suzuki_perfect ha hK).2
  have hns : ¬ Group.IsSolvable (suzukiGroup a K) := Group.IsPerfect.not_isSolvable _
  obtain ⟨e⟩ := (CFSG.RankThree.PartOne.TCX.Ree.b2_level D hK hperm hstab).1
  exact Or.inr ⟨e.symm.isSimpleGroup, fun _ =>
    hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective), Or.inr ⟨e⟩⟩

theorem typedOrBot_parabolic_fixed [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w') {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (J : Set (Fin ReeTag.F4.tag.rank))) :
    TypedOrBot K a (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n') := by
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · rw [rootSpan_parabolicRoots_empty, bot_inf_eq]
    exact Or.inl rfl
  · have hJ : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact typedOrBot_A1Pair D ha hK a1Pair_zero_two hn' hperm hstab
  · have hJ : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact typedOrBot_A1Pair D ha hK a1Pair_zero_three hn' hperm hstab
  · have hJ : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact typedOrBot_A1Pair D ha hK a1Pair_one_three hn' hperm hstab
  · have hJs : (J : Set (Fin ReeTag.F4.tag.rank)) = f4B2Support := by
      ext k
      constructor
      · intro hk
        have hk' := (h12 k).1 hk
        refine (mem_f4B2Support k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · intro hk
        have hk' := (mem_f4B2Support k).1 hk
        refine (h12 k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
    rw [hJs] at hstab ⊢
    exact typedOrBot_B2 D ha hK hperm hstab

end Parabolic

section Star

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

theorem typedStar [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    TypedOrBot K a (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) := by
  have hbp := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hord
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) hp hp3 hbp hb1 hw
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp (by omega) hbp hw hβ
  have hFN : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    D.isFrob.fext_canonicalRep u
  have hNad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L u
  have hnad : canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L w
  have hn'ad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹ ∈
      adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem hNad hnad) (inv_mem (Fext_mem D.F hNad))
  have hperm : PermAct (canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹)
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
    rw [hFN]
    exact ((permAct_canonicalRep u).mul (permAct_canonicalRep w)).mul
      (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv
  have key := typedOrBot_parabolic_fixed D ha hK hn'ad hperm hJ
    (fun γ hγ => smul_dualRoot_mem_parabolic hS w u hst hΦ hγ)
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
  rw [hΦ] at hmap
  refine TypedOrBot.of_map
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective ?_
  rw [hmap]
  exact key

end Star

section Master

variable {L : Type} [Field L] {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {a : ℕ} [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

theorem typed_frame
    {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hconj : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
      ∃ c : ReeTag.F4.reeGamma K a,
        g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L)
    (hrad : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      orderOf (rootDiagUnit ReeTag.F4.tag b) = p →
      rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n →
      TypedOrBot K a (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      ⁅Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))⁆ ≤ N ∧
      TypedOrBot K a N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hcH⟩ := hconj x hx
  let ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp (MulAut.conj c).toMonoidHom
  have hψ : ∀ d, ψ d = g₀⁻¹ * thetaGamma L a (c * d * c⁻¹) * g₀ := fun d => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h
    rw [hψ, hψ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
    exact h2
  have hψmem : ∀ d, ψ d ∈ adjointGroup ReeTag.F4.tag L := fun d => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg₀) (thetaGamma_mem_adjointGroup L _)) hg₀
  have hψtw : ∀ d, ψ d ∈ twistedFixed D.F n := fun d => by
    rw [hψ]
    exact conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L _) (D.fext_theta _)
  have hy : ψ x = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := hψ x
  have hyH : ψ x ∈ torusGroup ReeTag.F4.tag L := by rw [hy]; exact hcH
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hordy : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
    rw [← hb, orderOf_injective ψ hψinj x]
    exact hx
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hordy
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hordy
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hcommh : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * ψ d := by
    intro d hd
    rw [← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 hd
  have hHQ : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d ∈ (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) *
        (rootSpan ReeTag.F4.tag L (rootCharKernel b) : Set (ModGL ReeTag.F4.tag L)) :=
    fun d hd => mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn (fun _ h => h)
      (hψmem d) (hcommh d hd)
  set P : Subgroup (ModGL ReeTag.F4.tag L) :=
    rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n with hP
  have hPψ : ∀ u ∈ P, ∃ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d = u := by
    rintro u ⟨huQ, huT⟩
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀ hFg₀ huT
    obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
    have hθc : thetaGamma L a (c * x * c⁻¹) = g₀ * ψ x * g₀⁻¹ := by
      rw [hy]; group
    have huy : u * ψ x = ψ x * u := by
      rw [hb]
      exact Subgroup.mem_centralizer_singleton_iff.1
        (rootSpan_rootCharKernel_le_centralizer b huQ)
    have hcomm : γ * (c * x * c⁻¹) = (c * x * c⁻¹) * γ := by
      apply thetaGamma_injective L
      rw [map_mul (thetaGamma L a) γ (c * x * c⁻¹), map_mul (thetaGamma L a) (c * x * c⁻¹) γ, hγ,
        hθc]
      calc g₀ * u * g₀⁻¹ * (g₀ * ψ x * g₀⁻¹) = g₀ * (u * ψ x) * g₀⁻¹ := by group
        _ = g₀ * (ψ x * u) * g₀⁻¹ := by rw [huy]
        _ = g₀ * ψ x * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by group
    have hd : c⁻¹ * γ * c ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * γ * c) * x = c⁻¹ * (γ * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * γ) * c := by rw [hcomm]
        _ = x * (c⁻¹ * γ * c) := by group
    refine ⟨c⁻¹ * γ * c, hd, ?_⟩
    rw [hψ, show c * (c⁻¹ * γ * c) * c⁻¹ = γ by group, hγ]
    group
  have hrad' : TypedOrBot K a P := hrad b hordy (by rw [← hb]; exact hψtw x)
  set C : Subgroup (ReeTag.F4.reeGamma K a) :=
    Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) with hC
  let N : Subgroup (ReeTag.F4.reeGamma K a) := P.comap ψ ⊓ C
  have hNC : N ≤ C := inf_le_right
  have hCN : ⁅C, C⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun d₁ hd₁ d₂ hd₂ => ?_
    have hdC : ⁅d₁, d₂⁆ ∈ C := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)
    refine ⟨?_, hdC⟩
    show ψ ⁅d₁, d₂⁆ ∈ P
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hT : ψ d₁ * ψ d₂ * (ψ d₁)⁻¹ * (ψ d₂)⁻¹ ∈ twistedFixed D.F n :=
      (twistedFixed D.F n).mul_mem ((twistedFixed D.F n).mul_mem
        ((twistedFixed D.F n).mul_mem (hψtw d₁) (hψtw d₂))
        ((twistedFixed D.F n).inv_mem (hψtw d₁))) ((twistedFixed D.F n).inv_mem (hψtw d₂))
    exact ⟨commutator_mem_rootSpan hS (hHQ d₁ hd₁) (hHQ d₂ hd₂), hT⟩
  have hNP : N.map ψ = P := by
    ext u
    constructor
    · rintro ⟨d, ⟨hdP, -⟩, rfl⟩
      exact hdP
    · intro hu
      obtain ⟨d, hdC, rfl⟩ := hPψ u hu
      exact ⟨d, ⟨hu, hdC⟩, rfl⟩
  exact ⟨N, hNC, hCN, TypedOrBot.of_map ψ hψinj (by rw [hNP]; exact hrad')⟩

end Master

section Sector

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem typed_sector (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) (E : Subgroup (ModGL ReeTag.F4.tag L))
    (hEH : E ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (m : ℕ)
    (hE : Nat.card E = m ^ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpm : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2)
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      ⁅Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))⁆ ≤ N ∧
      TypedOrBot K a N := by
  obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF m hE hp hpm
  exact typed_frame D hg₀ hFg₀ hp hp3 hconj
    (fun b hordb hbT => typedStar D ha hK w hp hp3 hordb hbT) x hx

end Sector

theorem largeRee_layer_typed
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) ∨
      ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
        N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
        ⁅Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
          Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))⁆ ≤ N ∧
        IsSimpleGroup ↥N ∧
        (Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥N) ∨
          Nonempty (↥(suzukiGroup a K) ≃* ↥N)) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := hx ▸ orderOf_dvd_natCard x
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hfin : (∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      ⁅Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))⁆ ≤ N ∧
      TypedOrBot K a N) →
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) ∨
        ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
          N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
          ⁅Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
            Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))⁆ ≤ N ∧
          IsSimpleGroup ↥N ∧
          (Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥N) ∨
            Nonempty (↥(suzukiGroup a K) ≃* ↥N)) := by
    rintro ⟨N, hNC, hCN, hN | ⟨hs, -, hty⟩⟩
    · left
      subst hN
      exact isSolvable_of_commutator_le_bot hCN
    · exact Or.inr ⟨N, hNC, hCN, hs, hty⟩
  have hodd6 : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1 →
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) := by
    intro h
    have h2 := not_two_dvd_card_centralizer_of_sixTwelve ha hK hp hp3 h x hx
    have hodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))) :=
      Nat.odd_iff.2 (by omega)
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hdvd' := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp hp3 hdvd
  rcases hdvd' with h1 | h2 | h3 | h4 | h5
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi1 D.isFrob
    exact hfin (typed_sector D ha hK wPhi1 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi1 hK hp hp3 h1) x hx)
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi2 D.isFrob
    exact hfin (typed_sector D ha hK wPhi2 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp hp3 h2) x hx)
  · rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D.isFrob
      exact hfin (typed_sector D ha hK wPhi4p E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4p hK hp hp3 hpp) x hx)
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4m D.isFrob
      exact hfin (typed_sector D ha hK wPhi4m E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4m hK hp hp3 hpm) x hx)
  · exact Or.inl (hodd6 (Or.inl h4))
  · exact Or.inl (hodd6 (Or.inr h5))

end TypedLayer

section KD

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (SRT.isSolvable_fixSubgroup_of_congr)

set_option linter.unusedSectionVars false

theorem center_eq_bot_of_equiv_quasisimple {Y X : Type} [Group Y] [Group X] [IsSimpleGroup X]
    (hY : CFSG.Open.IsQuasisimple Y) (E : Y ≃* X) : Subgroup.center X = ⊥ := by
  refine center_eq_bot_of_simple ?_
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ u v : Y, u * v = v * u := fun u v =>
    E.injective (by rw [map_mul, map_mul, hcon])
  have hZ : Subgroup.center Y = ⊤ :=
    eq_top_iff.2 fun u _ => Subgroup.mem_center_iff.2 fun v => hcomm v u
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  obtain ⟨u, hu⟩ := exists_ne (1 : Y ⧸ Subgroup.center Y)
  induction u using QuotientGroup.induction_on with
  | H u => exact hu ((QuotientGroup.eq_one_iff u).2 (hZ ▸ Subgroup.mem_top u))

theorem nonempty_pSimple_equiv {G : Type} [Group G] [Finite G] {C I : Subgroup G}
    (hI : GLAPComponent 5 C I) {X : Type} [Group X] [IsSimpleGroup X] (E : barOf 5 I ≃* X) :
    Nonempty (PSimple 5 I ≃* X) :=
  ⟨pSimpleEquivOfBarEquiv E (center_eq_bot_of_equiv_quasisimple
    (Lemma1315b.isQuasisimple_barOf_of_comp (by norm_num) hI) E)⟩

theorem isSolvable_fixSubgroup_suzukiGroup_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {β : MulAut ↥(suzukiGroup 2 K)} (hβ : β ^ 5 = 1)
    (hβ1 : β ≠ 1) : Group.IsSolvable ↥(fixSubgroup β) := by
  have hp : (5 : ℕ).Prime := by norm_num
  haveI : Fact (5 : ℕ).Prime := ⟨hp⟩
  haveI hfin : Finite (suzukiGroup 2 K) := (suzuki_simple (by norm_num) hK).1
  have hord : orderOf β = 5 := orderOf_eq_prime hβ hβ1
  by_cases hin : β ∈ inner (suzukiGroup 2 K)
  · obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot (by norm_num) hK) hin hβ hβ1
    have hodd : Odd (orderOf x) := by
      rw [orderOf_eq_prime hxp hx1]
      decide
    obtain ⟨hcard, -⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers (by norm_num)
        hK).2 x hx1 hodd
    rw [fixSubgroup_conj]
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
  · obtain ⟨σ, h, b, k, _, _, -, hb, hk, hconj, ⟨efix⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent 2 (by norm_num) K hK 5 hp
        (by norm_num) β hord hin
    have hb0 : b = 0 := by omega
    subst hb0
    have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
    haveI : Finite (suzukiGroup 0 k) := finite_suzukiGroup hk
    have hcard := (suzuki_two_normal_five_complement_core_trivial hk2).1
    haveI hsolv : Group.IsSolvable (suzukiGroup 0 k) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
    have hφ : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β =
        szFieldAut 2 K σ := by
      have : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β =
          MulAut.conj h * β * (MulAut.conj h)⁻¹ := rfl
      rw [this, hconj]
    refine SRT.isSolvable_fixSubgroup_of_congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K)
      β ?_
    rw [hφ]
    exact Group.isSolvable_of_isSolvable_injective (f := efix.toMonoidHom) efix.injective

theorem congr_pow_five {S T : Type} [Group S] [Group T] (e : S ≃* T) {α : MulAut S}
    (hα : α ^ 5 = 1) : MulAut.congr e α ^ 5 = 1 := by
  rw [← map_pow, hα, map_one]

theorem congr_ne_one {S T : Type} [Group S] [Group T] (e : S ≃* T) {α : MulAut S}
    (hα1 : α ≠ 1) : MulAut.congr e α ≠ 1 :=
  fun h => hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))

theorem isSolvable_fixSubgroup_suzuki_five (hv : (TauCeti.LieTypeIndex.suzuki 2).Valid)
    {S : Type} [Group S] [Finite S] (e0 : S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group)
    {α : MulAut S} (hα : α ^ 5 = 1) (hα1 : α ≠ 1) : Group.IsSolvable ↥(fixSubgroup α) := by
  obtain ⟨-, a, -, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  have ha : a = 2 := by omega
  subst ha
  have hK : Nat.card K = 2 ^ (2 * 2 + 1) := by rw [hK', hf]
  exact SRT.isSolvable_fixSubgroup_of_congr (e0.trans θ) α
    (isSolvable_fixSubgroup_suzukiGroup_five hK (congr_pow_five _ hα) (congr_ne_one _ hα1))

theorem exc5_down_reeF4 (hv : (TauCeti.LieTypeIndex.reeF4 2).Valid)
    {S : Type} [Group S] [Finite S] (e0 : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group)
    {α : MulAut S} (hα : α ^ 5 = 1) (hα1 : α ≠ 1) {I : Subgroup S}
    (hI : GLAPComponent 5 (fixSubgroup α) I) : Claims1116.Exc5 (PSimple 5 I) := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index 2 hv e0
  obtain ⟨-, a, ha, hfa, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have ha2 : a = 2 := by omega
  subst ha2
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have hI' : GLAPComponent 5 (Lemma1314.fixSub α) I := by
    rw [PumpDefChar.fixSub_eq_fixSubgroup]
    exact hI
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field ha hK hp
      (congr_pow_five e hα) (congr_ne_one e hα1) with ⟨y, hy, hyp, hy1⟩ | ⟨σ, g, hσ, hβg⟩
  ·
    have hyo : orderOf y = 5 := orderOf_eq_prime hyp hy1
    rcases largeRee_layer_typed ha hK hp (by norm_num) y hyo with hsol | ⟨N, hNC, hCN, hNs, hty⟩
    · exfalso
      refine CFSG.HardMathSupport.Dickson.DefCharOuter.Export.not_glaPComponent_of_solvable ?_ hI
      refine SRT.isSolvable_fixSubgroup_of_congr e α ?_
      rw [hy, fixSubgroup_conj]
      exact hsol
    · have hC : fixSubgroup (MulAut.conj y) =
          Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 2)) := fixSubgroup_conj y
      have hNC' : N ≤ fixSubgroup (MulAut.conj y) := hC ▸ hNC
      have hCN' : ⁅fixSubgroup (MulAut.conj y), fixSubgroup (MulAut.conj y)⁆ ≤ N := by
        rw [hC]
        exact hCN
      haveI := normal_subgroupOf_of_commutator_le hCN'
      obtain ⟨E0⟩ := PumpDefChar.nonempty_barOf_equiv hp e hy hNC' hNs
        (isSolvable_quotient_of_commutator_le hCN') hI'
      haveI := hNs
      rcases hty with hf | hf
      · exfalso
        obtain ⟨f⟩ := hf
        have h5 := dvd_card_barOf hp hI
        rw [Nat.card_congr (E0.trans f.symm).toEquiv,
          CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK] at h5
        norm_num at h5
      · obtain ⟨f⟩ := hf
        obtain ⟨c⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_suzukiGroup_equiv_cat
            (by norm_num : 1 ≤ 2) hK
        obtain ⟨E1⟩ := nonempty_pSimple_equiv hI E0
        exact ⟨⟨.suzuki 2, _⟩, Or.inr (Or.inl rfl), ⟨E1.trans (f.symm.trans c)⟩⟩
  ·
    have hcongr := PumpDefChar.congr_trans_inv e α (MulAut.conj g)
      (ReeTag.F4.reeGammaFieldAut K 2 σ) hβg
    obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_fieldAut_equiv' hK hp hp2
        σ hσ
    obtain ⟨b', hb', hkcard', -⟩ :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
    have hb0 : b = 0 := by
      have h := hkcard.symm.trans hkcard'
      have := Nat.pow_right_injective (le_refl 2) h
      omega
    subst hb0
    haveI := hchar
    haveI : Finite (fixSubfield σ) := Subtype.finite
    have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hkcard]; norm_num
    obtain ⟨hs, -, ⟨hcat⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.commutator_reeGamma_F4_zero_data hk2
    set C := fixSubgroup (ReeTag.F4.reeGammaFieldAut K 2 σ) with hCdef
    set D : Subgroup ↥C := commutator ↥C with hD
    set J : Subgroup (ReeTag.F4.reeGamma K 2) := D.map C.subtype with hJ
    have hJC : J ≤ C := Subgroup.map_subtype_le _
    have hCJ : ⁅C, C⁆ ≤ J := by
      refine Subgroup.commutator_le.2 fun u hu v hv => ?_
      refine ⟨⁅(⟨u, hu⟩ : ↥C), ⟨v, hv⟩⁆, ?_, ?_⟩
      · rw [hD, commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · simp [commutatorElement_def]
    haveI := normal_subgroupOf_of_commutator_le hCJ
    have hmap : D.map eC.toMonoidHom = commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0) := by
      rw [hD, commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ eC.surjective]
    let eDR : ↥D ≃* ↥(commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0)) :=
      (D.equivMapOfInjective eC.toMonoidHom eC.injective).trans (MulEquiv.subgroupCongr hmap)
    let eJ : ↥J ≃* ↥(commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0)) :=
      (D.equivMapOfInjective C.subtype C.subtype_injective).symm.trans eDR
    haveI := hs
    haveI hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup
    obtain ⟨E0⟩ := PumpDefChar.nonempty_barOf_equiv hp _ hcongr hJC hJs
      (isSolvable_quotient_of_commutator_le hCJ) hI'
    obtain ⟨E1⟩ := nonempty_pSimple_equiv hI E0
    exact ⟨⟨.tits, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.tits_valid⟩, Or.inl rfl,
      ⟨E1.trans (eJ.trans hcat)⟩⟩

theorem exc5_down (S : Type) [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hS : Claims1116.Exc5 S) (α : MulAut S) (hα : α ^ 5 = 1)
    (I : Subgroup S) (hI : GLAPComponent 5 (fixSubgroup α) I) :
    Claims1116.Exc5 (PSimple 5 I) := by
  have hp : (5 : ℕ).Prime := by norm_num
  haveI := hs
  by_cases hα1 : α = 1
  · subst hα1
    rw [fixSubgroup_one_eq_top] at hI
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hna hI
    exact Claims1116.exc5_congr e.symm hS
  obtain ⟨⟨d, hd⟩, hidx, ⟨e0⟩⟩ := hS
  simp only at hidx
  rcases hidx with rfl | rfl | rfl
  · exact (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.not_glaPComponent_of_solvable
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_tits hd hna ⟨e0⟩ hp
        (by norm_num) hα hα1) hI).elim
  · exact (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.not_glaPComponent_of_solvable
      (isSolvable_fixSubgroup_suzuki_five hd e0 hα hα1) hI).elim
  · exact exc5_down_reeF4 hd e0 hα hα1 hI

end KD

section Config

theorem config_cases {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {e a : G} {J0 J1 : Subgroup G}
    (hae : a * e = e * a) (hap : a ^ p = 1) (hJ1 : GLAPComponent p (Cg e) J1)
    (hJ0 : GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0)
    (hKx : Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1) :
    (a ∈ Subgroup.normalizer (J1 : Set G) ∧
        GLAPComponent p (J1 ⊓ Subgroup.centralizer ({a} : Set G)) J0) ∨
      Nonempty (PSimple p J0 ≃* PSimple p J1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Js : Subgroup G := ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 with hJs
  rw [hKx] at hJ0
  have hcomp : ∀ g ∈ Subgroup.zpowers a, GLAPComponent p (Cg e) (GLBConj g J1) := by
    intro g hg
    have hge : g * e = e * g := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (Commute.zpow_left hae k).eq
    have := glaPComponent_gLBConj hJ1 g
    rwa [Prop1116Design.gLBConj_cg_eq hge] at this
  have hJsn : IsSubnormal Js (Cg e) := by
    have hJs' : Js = sSup ((fun g => GLBConj g J1) '' (Subgroup.zpowers a : Set G)) := by
      rw [hJs, sSup_image]
      rfl
    rw [hJs']
    exact CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp _
      (by rintro L ⟨g, hg, rfl⟩; exact hcomp g hg)
  have hlayer : IsSubnormal (GLAPLayer p (Js ⊓ Cg a)) (Js ⊓ Cg a) :=
    CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp
      {L | GLAPComponent p (Js ⊓ Cg a) L} fun _ h => h
  have hJ0a : GLAPComponent p (Js ⊓ Cg a) J0 := l119_glaPComponent_of_isSubnormal hp hlayer hJ0
  have hJ0' : GLAPComponent p (Cg e ⊓ Subgroup.centralizer ({a} : Set G)) J0 :=
    l119_glaPComponent_of_isSubnormal hp (isSubnormal_inf hJsn (Cg a)) hJ0a
  have hq1 : CFSG.Open.IsQuasisimple (barOf p J1) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barX_iff hp hJ1.2.1).1
      hJ1.2.2.1.2.2
  by_cases haN : a ∈ Subgroup.normalizer (J1 : Set G)
  ·
    have hJsJ : Js = J1 := by
      refine le_antisymm (iSup₂_le fun g hg => ?_) (le_iSup₂_of_le 1 (Subgroup.one_mem _) (by
        rw [gLBConj_one]))
      have hgN : g ∈ Subgroup.normalizer (J1 : Set G) :=
        (Subgroup.zpowers_le.2 haN) hg
      exact (mem_normalizer_iff_gLBConj_eq.1 hgN).le
    refine Or.inl ⟨haN, ?_⟩
    rw [← hJsJ]
    exact hJ0a
  ·
    have ha1 : a ≠ 1 := fun h => haN (h ▸ (Subgroup.normalizer (J1 : Set G)).one_mem)
    have haC : a ∈ Cg e := Subgroup.mem_centralizer_singleton_iff.2 hae
    have hle : barX p (Cg e) J0 ≤ barX p (Cg e) Js := barX_mono (hJ0a.1.trans inf_le_left)
    obtain ⟨π, hπs, hπk, -⟩ := Inputs183eqv.input18_3_eqv_holds G p hp hp2 (Cg e) J1
      (Subgroup.zpowers a) hJ1 (AltFacts5.isElemAbelian_zpowers hap) (Subgroup.zpowers_le.2 haC)
      a (Subgroup.mem_zpowers a) ha1 haC (Or.inl haN) J0 hJ0' hle
    obtain ⟨e1⟩ := Claims126.nonempty_quot_center_quot hq1.1 π.ker hπk
    exact Or.inr ⟨(Lemma1315b.centerQuotEquiv
      (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm).trans e1⟩

theorem transfer_step {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : a ^ p = 1) {L : Subgroup G}
    (hL : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L) :
    ∃ α : MulAut (PSimple p K), α ^ p = 1 ∧ ∃ I : Subgroup (PSimple p K),
      GLAPComponent p (fixSubgroup α) I ∧ Nonempty (PSimple p L ≃* PSimple p I) := by
  have hap' : IsPGroup p (Subgroup.zpowers a) :=
    Prop1116Design.elemAbelian_isPGroup (Claims1116.isElemAbelian_zpowers hap)
  exact ⟨_, CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one p K ha hap, _,
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp ha hap' hL,
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp ha hap' hL⟩

theorem exc5Down_of_kd {G : Type} [Group G] [Finite G]
    (hD : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Claims1116.Exc5 S → ∀ α : MulAut S, α ^ 5 = 1 →
        ∀ I : Subgroup S, GLAPComponent 5 (fixSubgroup α) I → Claims1116.Exc5 (PSimple 5 I))
    {e a : G} {J0 J1 : Subgroup G}
    (hae : a * e = e * a) (hap : a ^ 5 = 1) (hJ1 : GLAPComponent 5 (Cg e) J1)
    (hJ0 : GLAPComponent 5 (GLAPLayer 5 (Kx 5 J0 e ⊓ Cg a)) J0)
    (hKx : Kx 5 J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1)
    (hr : Claims1116.Exc5 (barOf 5 J1 ⧸ Subgroup.center (barOf 5 J1))) :
    Claims1116.Exc5 (barOf 5 J0 ⧸ Subgroup.center (barOf 5 J0)) := by
  have hp : (5 : ℕ).Prime := by norm_num
  rcases config_cases hp (by norm_num) hae hap hJ1 hJ0 hKx with ⟨haN, hJ0''⟩ | he2
  · obtain ⟨hsimple, hnonab⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hJ1
    obtain ⟨α, hα, I, hI, ⟨eJ⟩⟩ := transfer_step hp haN hap hJ0''
    exact Claims1116.exc5_congr eJ.symm (hD _ hsimple hnonab hr α hα I hI)
  · obtain ⟨e2⟩ := he2
    exact Claims1116.exc5_congr e2.symm hr

end Config

section Spor

theorem isLpType_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n Q : ℕ}
    (h : IsLpType n Q Y) : IsLpType n Q X := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFin, hc, ⟨e.trans f⟩⟩

theorem glaPComponent_top_fixSubgroup_one {S : Type} [Group S] [IsSimpleGroup S] {p : ℕ}
    (hnc : ∃ a b : S, a * b ≠ b * a) (hO : GLAPPrimeCore p S = ⊥) :
    GLAPComponent p (fixSubgroup (1 : MulAut S)) ⊤ := by
  rw [fixSubgroup_one_eq_top]
  refine Inputs1315.glaPComponent_self_of_quasisimple ?_ ?_
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).symm
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hnc)
  · rw [← glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).symm, hO,
      Subgroup.map_bot]

@[expose] def InputSporDownChev : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ s : TauCeti.SporadicName, IsSporType s S →
    ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (PSimple p I) →
      α ≠ 1 ∧
        ((p = 3 ∧ (s = .M23 ∨ s = .HS) ∧ IsLpType 2 5 (PSimple p I)) ∨
          (p = 3 ∧ (s = .M24 ∨ s = .He) ∧ IsLpType 2 7 (PSimple p I)) ∨
          (p = 5 ∧ s = .Suz ∧ IsLpType 2 9 (PSimple p I)) ∨
          (p = 13 ∧ s = .M ∧ IsLpType 3 3 (PSimple p I)))

end Spor

section Field

def cstar {Y : Type} [Group Y] (L : Subgroup Y) (b : Y) (X : Subgroup Y) : Subgroup Y where
  carrier := {o | o ∈ X ∧ o ∈ L ∧ ∃ z ∈ L ⊓ Subgroup.centralizer (L : Set Y), b * o * b⁻¹ = o * z}
  mul_mem' := by
    rintro x y ⟨hxX, hxL, z, hz, hxz⟩ ⟨hyX, hyL, w, hw, hyw⟩
    refine ⟨X.mul_mem hxX hyX, L.mul_mem hxL hyL, z * w,
      (L ⊓ Subgroup.centralizer (L : Set Y)).mul_mem hz hw, ?_⟩
    have hzy : y * z = z * y := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) y hyL
    calc b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
      _ = (x * z) * (y * w) := by rw [hxz, hyw]
      _ = x * (z * y) * w := by group
      _ = x * (y * z) * w := by rw [hzy]
      _ = x * y * (z * w) := by group
  one_mem' := ⟨X.one_mem, L.one_mem, 1, (L ⊓ Subgroup.centralizer (L : Set Y)).one_mem, by group⟩
  inv_mem' := by
    rintro x ⟨hxX, hxL, z, hz, hxz⟩
    refine ⟨X.inv_mem hxX, L.inv_mem hxL, z⁻¹,
      (L ⊓ Subgroup.centralizer (L : Set Y)).inv_mem hz, ?_⟩
    have hzx : x * z = z * x := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) x hxL
    calc b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
      _ = (x * z)⁻¹ := by rw [hxz]
      _ = (z * x)⁻¹ := by rw [hzx]
      _ = x⁻¹ * z⁻¹ := by group

theorem commutator_closure_le {Y : Type} [Group Y] {S : Set Y} {N : Subgroup Y}
    (hN : ∀ s ∈ S, s ∈ Subgroup.normalizer (N : Set Y)) (hc : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ N := by
  have hcl : Subgroup.closure S ≤ Subgroup.normalizer (N : Set Y) := (Subgroup.closure_le _).2 hN
  have hconj : ∀ g ∈ Subgroup.closure S, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (hcl hg) n).1 hn
  have hA : ∀ g ∈ Subgroup.closure S, ∀ t ∈ S, ⁅g, t⁆ ∈ N := by
    intro g hg t ht
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hc x hx t ht
    | one => simp
    | mul x y hx _ ihx ihy =>
      have e : ⁅x * y, t⁆ = x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hconj x hx _ ihy) ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, t⁆ = x⁻¹ * ⁅x, t⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj x⁻¹ ((Subgroup.closure S).inv_mem hx) _ (N.inv_mem ihx)
  rw [Subgroup.commutator_le]
  intro g hg h hh
  induction hh using Subgroup.closure_induction with
  | mem t ht => exact hA g hg t ht
  | one => simp
  | mul y₁ y₂ hy₁ _ ih₁ ih₂ =>
    have e : ⁅g, y₁ * y₂⁆ = ⁅g, y₁⁆ * (y₁ * ⁅g, y₂⁆ * y₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ih₁ (hconj y₁ hy₁ _ ih₂)
  | inv y hy ih =>
    have e : ⁅g, y⁻¹⁆ = y⁻¹ * ⁅g, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj y⁻¹ ((Subgroup.closure S).inv_mem hy) _ (N.inv_mem ih)

theorem conj_mem_iSup {Y : Type} [Group Y] {ι : Type*} {N : ι → Subgroup Y} {g : Y}
    (hg : ∀ i, ∀ n ∈ N i, g * n * g⁻¹ ∈ N i) : ∀ h ∈ ⨆ i, N i, g * h * g⁻¹ ∈ ⨆ i, N i := by
  intro h hh
  refine Subgroup.iSup_induction N (C := fun x => g * x * g⁻¹ ∈ ⨆ i, N i) hh
    (fun i x hx => Subgroup.mem_iSup_of_mem i (hg i x hx)) (by simp) fun x y hx hy => ?_
  have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx hy

theorem mem_normalizer_iSup {Y : Type} [Group Y] {ι : Type*} {N : ι → Subgroup Y} {g : Y}
    (hg : ∀ i, ∀ n ∈ N i, g * n * g⁻¹ ∈ N i) (hg' : ∀ i, ∀ n ∈ N i, g⁻¹ * n * g⁻¹⁻¹ ∈ N i) :
    g ∈ Subgroup.normalizer (((⨆ i, N i : Subgroup Y)) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_iSup hg h hh, fun hh => ?_⟩
  have := conj_mem_iSup hg' _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem exists_le_of_normalizes {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {𝓛 : Set (Subgroup Y)} {b : Y} (hb : orderOf b = p)
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X ⊤)
    (hbX : ∀ X ∈ 𝓛, b ∈ Subgroup.normalizer (X : Set Y))
    {R : Subgroup Y} (hR : GLAPComponent p (sSup 𝓛 ⊓ Subgroup.centralizer ({b} : Set Y)) R) :
    ∃ X ∈ 𝓛, R ≤ X := by
  classical
  set L : Subgroup Y := sSup 𝓛 with hL
  set ZL : Subgroup Y := L ⊓ Subgroup.centralizer (L : Set Y) with hZL
  set M : Subgroup Y := L ⊓ Subgroup.centralizer ({b} : Set Y) with hM
  have hp0 : 0 < p := hp.pos
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x :=
    fun X hX X' hX' hne x hx y hy =>
      Prop95Parts.Input18.comp_comm (hcomp X hX) (hcomp X' hX') hne hx hy
  have hXL : ∀ X ∈ 𝓛, X ≤ L := fun X hX => le_sSup hX
  have horb : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j = X := by
    intro X hX j
    induction j with
    | zero => exact Input183.orbA_zero b X
    | succ j ih =>
      rw [Input183.orbA_succ, ih]
      exact gLBConj_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hbX X hX))
  have hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j ∈ 𝓛 := fun X hX j => by
    rw [horb X hX j]
    exact hX
  have hOJ : ∀ X ∈ 𝓛, Input183.OJ b X = X := by
    intro X hX
    rw [Input183.OJ_eq_fin hb hp0]
    simp only [horb X hX]
    haveI : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
    exact iSup_const
  have hSO : ∀ X ∈ 𝓛, ∀ o ∈ Input183.OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      b * o * b⁻¹ = o * z → o ∈ cstar L b X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
    intro X hX o ho z hz h
    rw [hOJ X hX] at ho
    exact Subgroup.mem_sup_left ⟨ho, hXL X hX ho, z, hz, h⟩
  set 𝔉 : Set (Subgroup Y) := (fun X => Input183.OJ b X) '' 𝓛 with h𝔉
  have h𝔉fin : 𝔉.Finite := Set.Finite.image _ (Set.toFinite 𝓛)
  have hyp : ∀ O ∈ 𝔉, ∃ X ∈ 𝓛, Input183.OJ b X = O := by
    rintro O ⟨X, hX, rfl⟩
    exact ⟨X, hX, rfl⟩
  have hLle : L ≤ sSup 𝔉 := by
    rw [hL]
    refine sSup_le fun X hX => ?_
    exact (Input183.orbA_zero b X ▸ Input183.orbA_le_OJ b X 0).trans (le_sSup ⟨X, hX, rfl⟩)
  have hgen := Input183.gen_fin hbp hp0 hL hmem hcomm (fun X => cstar L b X) hSO 𝔉 h𝔉fin hyp
  set H : Subgroup Y :=
    (⨆ X ∈ {X | X ∈ 𝓛 ∧ Input183.OJ b X ∈ 𝔉}, cstar L b X) ⊔ ZL with hH
  have hMH : M ≤ H := by
    intro m hm
    refine hgen m (hLle (Subgroup.mem_inf.1 hm).1) ⟨1, ZL.one_mem, ?_⟩
    have hmb : m * b = b * m := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2
    calc b * m * b⁻¹ = m * b * b⁻¹ := by rw [hmb]
      _ = m * 1 := by group
  set N : Subgroup Y := ⨆ X : ↥𝓛, ((X : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y))
    with hN
  set S : Set Y := {g | (∃ X ∈ 𝓛, g ∈ cstar L b X) ∨ g ∈ ZL} with hS
  have hHS : H ≤ Subgroup.closure S := by
    refine sup_le (iSup₂_le fun X hX g hg => Subgroup.subset_closure (Or.inl ⟨X, hX.1, hg⟩))
      fun g hg => Subgroup.subset_closure (Or.inr hg)
  have hconjS : ∀ s ∈ S, ∀ X : ↥𝓛, ∀ n ∈ (X : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y),
      s * n * s⁻¹ ∈ (X : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y) := by
    rintro s (⟨X₁, hX₁, hs⟩ | hs) X n hn
    · obtain ⟨hsX, hsL, z, hz, hsz⟩ := hs
      have hnX : n ∈ (X : Subgroup Y) := (Subgroup.mem_inf.1 hn).1
      have hnb : n * b = b * n := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
      have hnL : n ∈ L := hXL X X.2 hnX
      by_cases hXX : X₁ = (X : Subgroup Y)
      · subst hXX
        refine Subgroup.mem_inf.2 ⟨(X : Subgroup Y).mul_mem ((X : Subgroup Y).mul_mem hsX hnX)
          ((X : Subgroup Y).inv_mem hsX), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have hzn : n * z = z * n := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) n hnL
        have hbn : b * n * b⁻¹ = n := by
          calc b * n * b⁻¹ = n * b * b⁻¹ := by rw [hnb]
            _ = n := by group
        have key : b * (s * n * s⁻¹) * b⁻¹ = s * n * s⁻¹ := by
          calc b * (s * n * s⁻¹) * b⁻¹ = (b * s * b⁻¹) * (b * n * b⁻¹) * (b * s * b⁻¹)⁻¹ := by group
            _ = (s * z) * n * (s * z)⁻¹ := by rw [hsz, hbn]
            _ = s * (z * n) * z⁻¹ * s⁻¹ := by group
            _ = s * (n * z) * z⁻¹ * s⁻¹ := by rw [hzn]
            _ = s * n * s⁻¹ := by group
        calc s * n * s⁻¹ * b = (b * (s * n * s⁻¹) * b⁻¹) * b := by rw [key]
          _ = b * (s * n * s⁻¹) := by group
      · have hsn : s * n = n * s := hcomm X₁ hX₁ X X.2 hXX s hsX n hnX
        have e : s * n * s⁻¹ = n := by rw [hsn]; group
        rw [e]
        exact hn
    · have hsn : n * s = s * n :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hs).2) n
          (hXL X X.2 (Subgroup.mem_inf.1 hn).1)
      have e : s * n * s⁻¹ = n := by rw [← hsn]; group
      rw [e]
      exact hn
  have hSinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    rintro s (⟨X₁, hX₁, hs⟩ | hs)
    · exact Or.inl ⟨X₁, hX₁, (cstar L b X₁).inv_mem hs⟩
    · exact Or.inr (ZL.inv_mem hs)
  have hNS : ∀ s ∈ S, s ∈ Subgroup.normalizer (N : Set Y) := fun s hs =>
    mem_normalizer_iSup (fun X n hn => hconjS s hs X n hn)
      (fun X n hn => hconjS s⁻¹ (hSinv s hs) X n hn)
  have hcS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N := by
    rintro s (⟨X₁, hX₁, hs⟩ | hs) t (⟨X₂, hX₂, ht⟩ | ht)
    · by_cases hXX : X₁ = X₂
      · subst hXX
        obtain ⟨hsX, hsL, z, hz, hsz⟩ := hs
        obtain ⟨htX, htL, w, hw, htw⟩ := ht
        refine Subgroup.mem_iSup_of_mem ⟨X₁, hX₁⟩ (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [commutatorElement_def]
          exact X₁.mul_mem (X₁.mul_mem (X₁.mul_mem hsX htX) (X₁.inv_mem hsX)) (X₁.inv_mem htX)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hzt : Commute z t :=
            ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) t htL).symm
          have hzw : Commute z w :=
            ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) w
              (Subgroup.mem_inf.1 hw).1).symm
          have hws : Commute w s :=
            ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2) s hsL).symm
          have hkey : b * ⁅s, t⁆ * b⁻¹ = ⁅s, t⁆ := by
            have e1 : b * ⁅s, t⁆ * b⁻¹ = ⁅b * s * b⁻¹, b * t * b⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
            rw [e1, hsz, htw]
            exact CFSG.HardMathSupport.Solomon.Coordinator.i183_commutatorElement_mul_mul hzt hzw
              hws
          calc ⁅s, t⁆ * b = (b * ⁅s, t⁆ * b⁻¹) * b := by rw [hkey]
            _ = b * ⁅s, t⁆ := by group
      · have hst : s * t = t * s := hcomm X₁ hX₁ X₂ hX₂ hXX s hs.1 t ht.1
        rw [commutatorElement_eq_one_iff_mul_comm.2 hst]
        exact N.one_mem
    · have hst : s * t = t * s :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ht).2) s hs.2.1
      rw [commutatorElement_eq_one_iff_mul_comm.2 hst]
      exact N.one_mem
    · have hts : t * s = s * t :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hs).2) t ht.2.1
      rw [commutatorElement_eq_one_iff_mul_comm.2 hts.symm]
      exact N.one_mem
    · have hts : t * s = s * t :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hs).2) t (Subgroup.mem_inf.1 ht).1
      rw [commutatorElement_eq_one_iff_mul_comm.2 hts.symm]
      exact N.one_mem
  have hHN : ⁅H, H⁆ ≤ N :=
    (Subgroup.commutator_mono hHS hHS).trans (commutator_closure_le hNS hcS)
  have hRN : R ≤ N := by
    rw [← glaPComponent_perfect hR]
    exact (Subgroup.commutator_mono (hR.1.trans hMH) (hR.1.trans hMH)).trans hHN
  have hNXM : ∀ X ∈ 𝓛, X ⊓ Subgroup.centralizer ({b} : Set Y) ≤ M := fun X hX =>
    inf_le_inf_right _ (hXL X hX)
  have hLN : ∀ X ∈ 𝓛, L ≤ Subgroup.normalizer (X : Set Y) := by
    intro X hX
    refine sSup_le fun X' hX' x hx => ?_
    by_cases h : X' = X
    · subst h
      exact Subgroup.le_normalizer hx
    · exact Input183.normalizer_of_commute fun s hs => hcomm X' hX' X hX h x hx s hs
  have hMnorm : ∀ X ∈ 𝓛, ∀ m ∈ M, m ∈ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer ({b} : Set Y) : Subgroup Y) : Set Y) := by
    intro X hX m hm
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hmX := Subgroup.mem_normalizer_iff.1 (hLN X hX (Subgroup.mem_inf.1 hm).1) n
    have hmC := Subgroup.mem_normalizer_iff.1
      (Subgroup.le_normalizer (Subgroup.mem_inf.1 hm).2) n
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at hmX hmC ⊢
    exact ⟨fun h => ⟨hmX.1 h.1, hmC.1 h.2⟩, fun h => ⟨hmX.2 h.1, hmC.2 h.2⟩⟩
  have hex : ∃ X ∈ 𝓛, R ≤ X ⊓ Subgroup.centralizer ({b} : Set Y) := by
    by_contra hno
    push Not at hno
    set T : Subgroup Y := ((Subgroup.centralizer
      ((barX p M R : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))).comap
        (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).map M.subtype with hT
    have hDT : ∀ X ∈ 𝓛, X ⊓ Subgroup.centralizer ({b} : Set Y) ≤ T := by
      intro X hX
      haveI : ((X ⊓ Subgroup.centralizer ({b} : Set Y)).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (hNXM X hX)).2 fun m hm => hMnorm X hX m hm
      rcases CFSG.HardMathSupport.Solomon.Coordinator.i183_le_or_commutator_eq_bot hp hR
          (hNXM X hX) with h | h
      · exact absurd h (hno X hX)
      · refine (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff (hNXM X hX)).1 ?_
        rw [Subgroup.commutator_comm] at h
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hNT : N ≤ T := iSup_le fun X => hDT X X.2
    have hRT : R ≤ T := hRN.trans hNT
    have hRc : barX p M R ≤ Subgroup.centralizer
        ((barX p M R : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hR.1).2 hRT
    obtain ⟨r, hr, t, ht, hrt⟩ := Input183.exists_noncomm_of_isComponentOf hR.2.2.1
    exact hrt ((Subgroup.mem_centralizer_iff.1 (hRc ht)) r hr)
  obtain ⟨X, hX, hRX⟩ := hex
  exact ⟨X, hX, hRX.trans inf_le_left⟩

theorem le_of_barX_le_comp {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C K' J : Subgroup G} {b : G} (hbC : b ∈ C) (hK' : GLAPComponent p C K')
    (hbK : b ∈ Subgroup.normalizer (K' : Set G)) (hbp : b ^ p = 1)
    (hJ : GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) J)
    (hle : barX p C J ≤ barX p C K') : J ≤ K' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd : IsPGroup p (Subgroup.zpowers b) :=
    Prop1116Design.elemAbelian_isPGroup (Claims1116.isElemAbelian_zpowers hbp)
  set A : Subgroup G := K' ⊓ Subgroup.centralizer ({b} : Set G) with hA
  have hAC : A ≤ C := inf_le_left.trans hK'.1
  set ψ := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hψ
  have h0 := Prop126b.glaPComponent_barX_inf_centralizer hp hbC (le_refl C)
    (Subgroup.le_normalizer hbC) hd hJ
  rw [barX_self] at h0
  have h1 : GLAPComponent p (barX p C K' ⊓ Subgroup.centralizer
      ({ψ ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C))) (barX p C J) :=
    glaPComponent_of_le hp h0 (le_inf hle (h0.1.trans inf_le_right)) (inf_le_inf_right _ le_top)
  have hmap : (A.subgroupOf C).map ψ = barX p C K' ⊓ Subgroup.centralizer
      ({ψ ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    barX_inf_centralizer hp hbC hK'.1 hbK hd
  rw [← hmap] at h1
  have hker : Nat.Coprime p (Nat.card ↥((A.subgroupOf C) ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨J₀, hJ₀, hJ₀map⟩ := exists_glaPComponent_map_eq hp ψ hker h1
  have hker' : Nat.Coprime p (Nat.card ↥((A.subgroupOf C) ⊓ C.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hJ' : GLAPComponent p A (J₀.map C.subtype) := by
    have h := glaPComponent_map hp C.subtype hker' hJ₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hAC] at h
  have hAsn : IsSubnormal A (C ⊓ Subgroup.centralizer ({b} : Set G)) := isSubnormal_inf hK'.2.1 _
  have hJ'' : GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) (J₀.map C.subtype) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183v_comp_up hp hJ' (inf_le_inf_right _ hK'.1)
      (isSubnormal_trans' hJ'.2.1 hAsn)
  have hsub : (J₀.map C.subtype).subgroupOf C = J₀ :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective J₀
  have hbar : barX p C J = barX p C (J₀.map C.subtype) := by
    show barX p C J = ((J₀.map C.subtype).subgroupOf C).map ψ
    rw [hsub, hJ₀map]
  have heq := Inputs183eqv.eq_of_barX_eq hp inf_le_left hJ hJ'' hbar
  rw [heq]
  exact hJ'.1.trans inf_le_left

def q3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

theorem valid_A_two_q3 : (TauCeti.LieTypeIndex.A 2 q3).Valid := by
  simp [q3]

theorem isLieOverField_of_isLpType_three_three {X : Type} [Group X]
    (h : IsLpType 3 3 (X ⧸ Subgroup.center X)) : Prop1116Design.IsLieOverField 3 X := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  haveI : Fact q3.p.Prime := ⟨Nat.prime_three⟩
  have hc' : Nat.card F = 3 ^ 1 := by rw [hc]; norm_num
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 3 3 1 (by norm_num) hc'
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q3 valid_A_two_q3
  refine ⟨⟨.A 2 q3, valid_A_two_q3⟩, ⟨(f.trans eK).trans eC.symm⟩, ?_⟩
  show (TauCeti.LieTypeIndex.A 2 q3).fieldOrder = 3
  rw [TauCeti.LieTypeIndex.fieldOrder_A, TauCeti.PrimePower.card_def]
  rfl

theorem isLieOverField_congr {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {Q : ℕ}
    (h : Prop1116Design.IsLieOverField Q X') : Prop1116Design.IsLieOverField Q X := by
  obtain ⟨idx, ⟨f⟩, hQ⟩ := h
  exact ⟨idx, ⟨(Claims1116.centerQuotEquiv e).trans f⟩, hQ⟩

theorem nonempty_pSimple_equiv_of_fixSubgroup_one {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore p Y = ⊥) {I : Subgroup Y}
    (hI : GLAPComponent p (fixSubgroup (1 : MulAut Y)) I) :
    Nonempty (PSimple p I ≃* (Y ⧸ Subgroup.center Y)) := by
  rw [fixSubgroup_one_eq_top] at hI
  have hqt : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).symm hq
  have hIt : I = ⊤ := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.i183v_eq_or_le_center hI.2.1 hqt with h | h
    · exact h
    · exfalso
      have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
      apply CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hI
      rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨z, hz, rfl⟩ := h hx
      have hzy := Subgroup.mem_center_iff.1 hz ⟨y, Subgroup.mem_top y⟩
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (congrArg Subtype.val hzy).symm
  subst hIt
  have hOt : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
    rw [← glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).symm, hO,
      Subgroup.map_bot]
  let E : barOf p (⊤ : Subgroup Y) ≃* Y :=
    ((QuotientGroup.quotientMulEquivOfEq hOt).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  exact ⟨Claims1116.centerQuotEquiv E⟩

@[expose] def InputL33Down : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 13 Y = ⊥ →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 13 →
      CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (Y ⧸ Subgroup.center Y) →
    ∀ β : MulAut Y, β ^ 13 = 1 → β ≠ 1 → ∀ I : Subgroup Y, GLAPComponent 13 (fixSubgroup β) I →
      IsLpType 3 3 (PSimple 13 I) → IsLpType 3 (3 ^ 13) Y ∨ Prop1116Design.IsLieOverField 3 Y

theorem input14_4_1Field_of_input (h : InputL33Down) : Claims1116.Input14_4_1Field := by
  intro G _ _ a e K J0 A0 q hK hq hq2 hq13 hchev hA0C hA0el heA0 he1 hJ0 hJ0K hL33
  classical
  have hp : (13 : ℕ).Prime := by norm_num
  have hp2 : (13 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (13 : ℕ).Prime := ⟨hp⟩
  set C := Cg a with hCdef
  have heC : e ∈ C := hA0C heA0
  have hep : e ^ 13 = 1 := hA0el.2 e heA0
  have hJ0' : GLAPComponent 13 (C ⊓ Subgroup.centralizer ({e} : Set G)) J0 := by
    have h1 : Cg2 e a = C ⊓ Subgroup.centralizer ({e} : Set G) := Input183.centralizer_pair_eq e a
    rw [← h1]
    exact hJ0
  have hJL : barX 13 C J0 ≤ barX 13 C (⨆ y ∈ A0, GLBConj y K) := barX_mono hJ0K
  have hq1 : CFSG.Open.IsQuasisimple (barOf 13 K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  by_cases heN : e ∈ Subgroup.normalizer (K : Set G)
  ·
    set ψ := QuotientGroup.mk' (GLAPPrimeCore 13 ↥C) with hψ
    have hA0ab : ∀ x ∈ A0, ∀ y ∈ A0, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hA0el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hcommB : ∀ x (hx : x ∈ A0) (z : ↥C), (z : G) ∈ A0 →
        ψ ⟨x, hA0C hx⟩ * ψ z = ψ z * ψ ⟨x, hA0C hx⟩ := by
      intro x hx z hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA0ab x hx z hz)
    have hbb1 : ψ ⟨e, heC⟩ ≠ 1 := by
      intro h1
      apply he1
      have hpow : (⟨e, heC⟩ : ↥C) ^ 13 = 1 := Subtype.ext (by simpa using hep)
      have h2 := l119_eq_one_of_pow_of_mem_core hp hpow ((QuotientGroup.eq_one_iff _).1 h1)
      exact congrArg Subtype.val h2
    have hbbord : orderOf (ψ ⟨e, heC⟩) = 13 :=
      orderOf_eq_prime (Lemma129b.mk_pow_eq_one heC hep) hbb1
    have hcomp : ∀ X ∈ Prop126b.Fam 13 C K (A0.subgroupOf C), IsComponentOf X ⊤ :=
      Prop126b.Fam_comp hK (A0.subgroupOf C)
    have hconjC : ∀ y ∈ A0, GLBConj y K ≤ C := fun y hy => by
      have h := gLBConj_mono y hK.1
      rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hA0C hy))] at h
    have hLbar : barX 13 C (⨆ y ∈ A0, GLBConj y K) ≤
        sSup (Prop126b.Fam 13 C K (A0.subgroupOf C)) := by
      have hSC : (⨆ y ∈ A0, GLBConj y K) ≤ C := iSup₂_le hconjC
      rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hSC]
      refine iSup₂_le fun y hy => ?_
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff (hconjC y hy),
        barX_gLBConj_eq 13 (hA0C hy) K]
      exact le_sSup ⟨⟨y, hA0C hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    have hJb0 : GLAPComponent 13 (⊤ ⊓ Subgroup.centralizer
        ({ψ ⟨e, heC⟩} : Set (↥C ⧸ GLAPPrimeCore 13 ↥C))) (barX 13 C J0) := by
      have h := Prop126b.glaPComponent_barX_inf_centralizer hp heC (le_refl C)
        (Subgroup.le_normalizer heC) (l119_isPGroup_zpowers hep) hJ0'
      rwa [barX_self] at h
    have hJb : GLAPComponent 13 (sSup (Prop126b.Fam 13 C K (A0.subgroupOf C)) ⊓
        Subgroup.centralizer ({ψ ⟨e, heC⟩} : Set (↥C ⧸ GLAPPrimeCore 13 ↥C))) (barX 13 C J0) :=
      glaPComponent_of_le hp hJb0 (le_inf (hJL.trans hLbar) (hJb0.1.trans inf_le_right))
        (inf_le_inf_right _ le_top)
    have hbK : ψ ⟨e, heC⟩ ∈ Subgroup.normalizer
        ((barX 13 C K : Subgroup (↥C ⧸ GLAPPrimeCore 13 ↥C)) : Set (↥C ⧸ GLAPPrimeCore 13 ↥C)) :=
      Claims1116.bar_mem_normalizer hK.1 heC (mem_normalizer_iff_gLBConj_eq.1 heN)
    have hbX : ∀ X ∈ Prop126b.Fam 13 C K (A0.subgroupOf C),
        ψ ⟨e, heC⟩ ∈ Subgroup.normalizer (X : Set (↥C ⧸ GLAPPrimeCore 13 ↥C)) := by
      rintro X ⟨z, hz, rfl⟩
      exact (l119_normalizer_gLBConj_iff (hcommB e heA0 z (Subgroup.mem_subgroupOf.1 hz))
        (barX 13 C K)).2 hbK
    obtain ⟨X, ⟨z, hz, rfl⟩, hJX⟩ := exists_le_of_normalizes hp hbbord hcomp hbX hJb
    have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
    set K' : Subgroup G := GLBConj (z : G) K with hK'def
    have hK' : GLAPComponent 13 C K' := by
      have h := glaPComponent_gLBConj hK (z : G)
      rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer z.2)] at h
    have heK' : e ∈ Subgroup.normalizer (K' : Set G) :=
      (l119_normalizer_gLBConj_iff (hA0ab e heA0 z hzA) K).2 heN
    have hle : barX 13 C J0 ≤ barX 13 C K' := by
      rw [hK'def, barX_gLBConj_eq 13 z.2 K]
      exact hJX
    have hJ0K' : J0 ≤ K' := le_of_barX_le_comp hp heC hK' heK' hep hJ0' hle
    have hJ0c : GLAPComponent 13 (K' ⊓ Subgroup.centralizer ({e} : Set G)) J0 :=
      glaPComponent_of_le hp hJ0' (le_inf hJ0K' (hJ0'.1.trans inf_le_right))
        (inf_le_inf_right _ hK'.1)
    have hep' : IsPGroup 13 (Subgroup.zpowers e) :=
      Prop1116Design.elemAbelian_isPGroup (Claims1116.isElemAbelian_zpowers hep)
    have hI := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_pQuotHom hp heK' hep' hJ0c
    have hJ0sub : GLAPComponent 13
        (fixSubgroup (K'.normalizerMonoidHom ⟨e, heK'⟩)) (J0.subgroupOf K') := by
      rw [CFSG.LocalAnalysis.GLTheoremA.fixSubgroup_normalizerMonoidHom heK']
      exact Prop126b.glaPComponent_subgroupOf hp inf_le_left hJ0c
    obtain ⟨g⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pQuot_equiv_subgroupOf 13 hJ0K'
    obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map hp
      (CFSG.LocalAnalysis.GLTheoremA.pQuotHom 13 K') hJ0sub hI
    have e₀ : PSimple 13 J0 ≃* PSimple 13 (J0.subgroupOf K') :=
      QuotientGroup.congr _ _ g.symm (Subgroup.map_center_eq g.symm)
    have hβ : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 13 K' ⟨e, heK'⟩ ^ 13 = 1 := by
      rw [← map_pow]
      have : (⟨e, heK'⟩ : ↥(Subgroup.normalizer (K' : Set G))) ^ 13 = 1 :=
        Subtype.ext (by simpa using hep)
      rw [this, map_one]
    have hqY : CFSG.Open.IsQuasisimple (barOf 13 K') :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK'
    have hOY : GLAPPrimeCore 13 (barOf 13 K') = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K') 13
    let eKK' : barOf 13 K ≃* barOf 13 K' := conjQuotEquiv 13 (z : G) K
    have hchevY : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q
        (barOf 13 K' ⧸ Subgroup.center (barOf 13 K')) :=
      Claims1116.isChevSimple_congr (Claims1116.centerQuotEquiv eKK') hchev
    have hLI : IsLpType 3 3 (PSimple 13 ((J0.subgroupOf K').map
        (CFSG.LocalAnalysis.GLTheoremA.pQuotHom 13 K'))) :=
      isLpType_congr (e₀.trans e₁).symm hL33
    by_cases hβ1 : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 13 K' ⟨e, heK'⟩ = 1
    ·
      rw [hβ1] at hI
      obtain ⟨E1⟩ := nonempty_pSimple_equiv_of_fixSubgroup_one hqY hOY hI
      exact Or.inr (isLieOverField_congr eKK'
        (isLieOverField_of_isLpType_three_three (isLpType_congr E1.symm hLI)))
    · rcases h (barOf 13 K') hqY hOY q hq hq2 hq13 hchevY _ hβ hβ1 _ hI hLI with h1 | h1
      · exact Or.inl (isLpType_congr eKK' h1)
      · exact Or.inr (isLieOverField_congr eKK' h1)
  ·
    obtain ⟨π, hπs, hπk, -⟩ := Inputs183eqv.input18_3_eqv_holds G 13 hp hp2 C K A0 hK hA0el hA0C
      e heA0 he1 heC (Or.inl heN) J0 hJ0' hJL
    obtain ⟨e1⟩ := Claims126.nonempty_quot_center_quot hq1.1 π.ker hπk
    have e2 : PSimple 13 J0 ≃* PSimple 13 K :=
      (Lemma1315b.centerQuotEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm).trans e1
    exact Or.inr (isLieOverField_of_isLpType_three_three (isLpType_congr e2.symm hL33))

end Field

section Main

set_option linter.unusedSectionVars false

theorem input14_9_10Down_holds : Claims1116.Input14_9_10Down := by
  intro G _ _ e a J0 J1 hae hap hJ1 hJ0 hKx hexc
  exact exc5Down_of_kd (fun S _ _ hs hna hS α hα I hI => exc5_down S hs hna hS α hα I hI)
    hae hap hJ1 hJ0 hKx hexc

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116b
