module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.RankThree.PartOne.TCX.Ree.A1Layer
import CFSG.RankThree.PartOne.TCX.Ree.B2Layer
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorSixTwelve
public import CFSG.RankThree.PartOne.KLR.SectorTori
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartOne.TCF.Pow2
public import CFSG.RankThree.PartOne.TCF.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.TCF
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise commutatorElement

private def ChevOrBot {G : Type} [Group G] (P : Subgroup G) : Prop :=
  P = ⊥ ∨ (IsSimpleGroup ↥P ∧ ¬ Group.IsSolvable ↥P ∧ LieFactorData 2 ↥P ∧
    (LieOrderBridge → IsEmpty (↥P ≃* alternatingGroup (Fin 6))))

private theorem ChevOrBot.simpleOrBot {G : Type} [Group G] {P : Subgroup G} (h : ChevOrBot P) :
    SimpleOrBot P := by
  rcases h with h | ⟨hs, hns, -, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨hs, hns⟩

private theorem ChevOrBot.of_mulEquiv {G H : Type} [Group G] [Group H] {P : Subgroup G}
    {Q : Subgroup H} (e : ↥P ≃* ↥Q) (h : ChevOrBot P) : ChevOrBot Q := by
  rcases h with rfl | ⟨hs, hns, hl, ha6⟩
  · left
    have : Subsingleton ↥Q := e.symm.injective.subsingleton
    exact Subgroup.eq_bot_of_subsingleton Q
  · right
    have := hs
    refine ⟨e.symm.isSimpleGroup, fun hsol => hns ?_, hl.of_mulEquiv e,
      fun hb => ⟨fun f => (ha6 hb).false (e.trans f)⟩⟩
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem ChevOrBot.of_map {G H : Type} [Group G] [Group H] {P : Subgroup G} (f : G →* H)
    (hf : Function.Injective f) (h : ChevOrBot (P.map f)) : ChevOrBot P :=
  h.of_mulEquiv (P.equivMapOfInjective f hf).symm

private theorem chevOrBot_of_mulEquiv_chev {G₀ G : Type} [Group G₀] [Group G] [IsSimpleGroup G₀]
    (hns : ¬ Group.IsSolvable G₀) (hl : LieFactorData 2 G₀)
    (ha6 : LieOrderBridge → IsEmpty (G₀ ≃* alternatingGroup (Fin 6))) {P : Subgroup G}
    (e : G₀ ≃* ↥P) : ChevOrBot P :=
  Or.inr ⟨e.symm.isSimpleGroup, fun _ =>
    hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective),
    hl.of_mulEquiv e, fun hb => ⟨fun f => (ha6 hb).false (e.trans f)⟩⟩

private theorem eight_le_card_of_card_eq {K : Type} {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : 8 ≤ Nat.card K := by
  rw [hK]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem isEmpty_SL2_mulEquiv_alternating_six {K : Type} [Field K] [Finite K] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsEmpty (Matrix.SpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  have h360 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hsl := CFSG.OrderReductions.LinearOrders.card_specialLinear K 2 (by norm_num)
  have h8 := eight_le_card_of_card_eq ha hK
  have hge : 8 * (8 ^ 2 - 1) ≤ Nat.card K * (Nat.card K ^ 2 - 1) :=
    Nat.mul_le_mul h8 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h8 2) 1)
  rw [h360] at hsl
  simp at hsl
  omega

section Parabolic

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

private theorem chevOrBot_A1Pair [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (h : A1Pair i j) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    ChevOrBot (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n') := by
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 ha hK
  have hns : ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
    obtain ⟨x, y, hxy⟩ := CFSG.LieType.Ree.LargeReeInvolution.exists_SL2_mul_ne_mul (K := K)
    intro hs
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.2 hs) x y)
  have h4 : 4 ≤ Nat.card K := (by norm_num : 4 ≤ 8).trans (eight_le_card_of_card_eq ha hK)
  obtain ⟨e⟩ := (CFSG.RankThree.PartOne.TCX.Ree.a1_level D h hK hn' hperm hstab).1
  exact chevOrBot_of_mulEquiv_chev hns (lieFactorData_SL2 h4)
    (fun _ => isEmpty_SL2_mulEquiv_alternating_six ha hK) e

private theorem chevOrBot_B2 [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    ChevOrBot (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
      twistedFixed D.F n') := by
  obtain ⟨hfin, hnt, hsimp⟩ := suzuki_simple ha hK
  have hperf := (suzuki_perfect ha hK).2
  have hns : ¬ Group.IsSolvable (suzukiGroup a K) := Group.IsPerfect.not_isSolvable _
  obtain ⟨e⟩ := (CFSG.RankThree.PartOne.TCX.Ree.b2_level D hK hperm hstab).1
  exact chevOrBot_of_mulEquiv_chev hns (lieFactorData_suzukiGroup ha hK)
    (fun hb => isEmpty_mulEquiv_alternating_six hb ⟨.suzuki a, suzuki_valid ha⟩
      (nonempty_suzukiGroup_equiv_cat ha hK)) e

private theorem chevOrBot_parabolic_fixed [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w') {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (J : Set (Fin ReeTag.F4.tag.rank))) :
    ChevOrBot (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n') := by
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · rw [rootSpan_parabolicRoots_empty, bot_inf_eq]
    exact Or.inl rfl
  · have hJ : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact chevOrBot_A1Pair D ha hK a1Pair_zero_two hn' hperm hstab
  · have hJ : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact chevOrBot_A1Pair D ha hK a1Pair_zero_three hn' hperm hstab
  · have hJ : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact chevOrBot_A1Pair D ha hK a1Pair_one_three hn' hperm hstab
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
    exact chevOrBot_B2 D ha hK hperm hstab

end Parabolic

section Star

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

private theorem chevStarSimple [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ChevOrBot (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
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
  have key := chevOrBot_parabolic_fixed D ha hK hn'ad hperm hJ
    (fun γ hγ => smul_dualRoot_mem_parabolic hS w u hst hΦ hγ)
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
  rw [hΦ] at hmap
  refine ChevOrBot.of_map
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective ?_
  rw [hmap]
  exact key

end Star

section Master

variable {L : Type} [Field L] {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {a : ℕ} [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

private def StarChev (n : ModGL ReeTag.F4.tag L) (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) : Prop :=
  ChevOrBot (rootSpan ReeTag.F4.tag L S ⊓ twistedFixed D.F n)

private theorem component_data_of_frame_chev
    {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hconj : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
      ∃ c : ReeTag.F4.reeGamma K a,
        g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L)
    (hrad : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      orderOf (rootDiagUnit ReeTag.F4.tag b) = p →
      rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n →
      StarChev D n (rootCharKernel b))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
        CFSG.RankThree.PartOne.IsComponentOf
          (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' → D' = N) ∧
      (N ≠ ⊥ → CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) ∧
      (N ≠ ⊥ → IsSimpleGroup ↥N ∧ LieFactorData 2 ↥N ∧
        (LieOrderBridge → IsEmpty (↥N ≃* alternatingGroup (Fin 6)))) := by
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
  have hL2 : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : PerfectRing L 2 := PerfectField.toPerfectRing 2
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃+* L, ∀ c, σ c = c ^ 2 :=
    ⟨frobeniusEquiv L 2, fun c => by simp [frobeniusEquiv_apply, frobenius_def]⟩
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
  have hrad' : ChevOrBot P := hrad b hordy (by rw [← hb]; exact hψtw x)
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
  have h2 : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N := by
    rintro g hg ⟨k, hk⟩
    have h1 : ψ g ^ (2 ^ k) = 1 := by
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    exact ⟨⟨mem_rootSpan_of_pow_two_pow_eq_one σ hσ hS (hHQ g hg) h1, hψtw g⟩, hg⟩
  have hNP : N.map ψ = P := by
    ext u
    constructor
    · rintro ⟨d, ⟨hdP, -⟩, rfl⟩
      exact hdP
    · intro hu
      obtain ⟨d, hdC, rfl⟩ := hPψ u hu
      exact ⟨d, ⟨hu, hdC⟩, rfl⟩
  have hNs : ChevOrBot N := ChevOrBot.of_map ψ hψinj (by rw [hNP]; exact hrad')
  refine ⟨N, hNC, h2, fun D' hD' => component_eq_of_simpleOrBot hNC hCN hNs.simpleOrBot hD',
    fun hN1 => isComponentOf_of_simpleOrBot hNC hCN hNs.simpleOrBot hN1, fun hN1 => ?_⟩
  rcases hNs with h | ⟨hs, -, hl, ha6⟩
  · exact absurd h hN1
  · exact ⟨hs, hl, ha6⟩

end Master

section Sector

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

private theorem layer_of_sector_chev (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) (E : Subgroup (ModGL ReeTag.F4.tag L))
    (hEH : E ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) (m : ℕ)
    (hE : Nat.card E = m ^ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpm : p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ m ^ 2)
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
        CFSG.RankThree.PartOne.IsComponentOf
          (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' → D' = N) ∧
      (N ≠ ⊥ → CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) ∧
      (N ≠ ⊥ → IsSimpleGroup ↥N ∧ LieFactorData 2 ↥N ∧
        (LieOrderBridge → IsEmpty (↥N ≃* alternatingGroup (Fin 6)))) := by
  obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF m hE hp hpm
  exact component_data_of_frame_chev D hg₀ hFg₀ hp hp3 hconj
    (fun b hordb hbT => chevStarSimple D ha hK w hp hp3 hordb hbT) x hx

end Sector

theorem largeRee_component_chev
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
        CFSG.RankThree.PartOne.IsComponentOf
          (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' → D' = N) ∧
      (N ≠ ⊥ → CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) ∧
      (N ≠ ⊥ → IsSimpleGroup ↥N ∧ LieFactorData 2 ↥N ∧
        (LieOrderBridge → IsEmpty (↥N ≃* alternatingGroup (Fin 6)))) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := hx ▸ orderOf_dvd_natCard x
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd6 : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1 →
      ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
        N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
        (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
          (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
        (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
          CFSG.RankThree.PartOne.IsComponentOf
            (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' → D' = N) ∧
        (N ≠ ⊥ → CFSG.RankThree.PartOne.IsComponentOf
          (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) ∧
        (N ≠ ⊥ → IsSimpleGroup ↥N ∧ LieFactorData 2 ↥N ∧
          (LieOrderBridge → IsEmpty (↥N ≃* alternatingGroup (Fin 6)))) := by
    intro h
    have h2 := not_two_dvd_card_centralizer_of_sixTwelve ha hK hp hp3 h x hx
    have hodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))) :=
      Nat.odd_iff.2 (by omega)
    refine ⟨⊥, bot_le, ?_, ?_, fun h => absurd rfl h, fun h => absurd rfl h⟩
    · rintro g hg ⟨k, hk⟩
      have hgo : orderOf (⟨g, hg⟩ : Subgroup.centralizer ({x} : Set _)) ∣
          Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hk] at hgo
      have hk0 : k = 0 := by
        by_contra hk0
        have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
        exact h2 (h2dvd.trans hgo)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      rw [hk]
      exact Subgroup.one_mem _
    · rintro D' ⟨hD'C, hD'q, -⟩
      exfalso
      have hodd' : Odd (Nat.card D') := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hD'C)
      have hsol : Group.IsSolvable D' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
      have : Group.IsPerfect D' := hD'q.1
      have := CFSG.LocalCores.isQuasisimple_nontrivial hD'q
      exact Group.IsPerfect.not_isSolvable D' hsol
  have hdvd' := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp hp3 hdvd
  rcases hdvd' with h1 | h2 | h3 | h4 | h5
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi1 D.isFrob
    exact layer_of_sector_chev D ha hK wPhi1 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi1 hK hp hp3 h1) x hx
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi2 D.isFrob
    exact layer_of_sector_chev D ha hK wPhi2 E hEH hEF _ hE hp hp3
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp hp3 h2) x hx
  · rcases dvd_phi4_cases hp hp3 h3 with ⟨hpp, -⟩ | ⟨hpm, -⟩
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D.isFrob
      exact layer_of_sector_chev D ha hK wPhi4p E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4p hK hp hp3 hpp) x hx
    · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4m D.isFrob
      exact layer_of_sector_chev D ha hK wPhi4m E hEH hEF _ hE hp hp3
        (pow_factorization_card_reeGamma_dvd_phi4m hK hp hp3 hpm) x hx
  · exact hodd6 (Or.inl h4)
  · exact hodd6 (Or.inr h5)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
