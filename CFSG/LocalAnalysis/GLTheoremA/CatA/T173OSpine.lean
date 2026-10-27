module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XLift
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XRank
import CFSG.GroupTheory.PerfectLeSupCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X

theorem stdExtendsN_of_stdExtends {p : ℕ} {G₀ : Type} [Group G₀] {A : Subgroup G₀} {d : G₀}
    (h : StdExtends p A d)
    (hT : ∃ T : Subgroup G₀, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ stdLayer d) :
    StdExtendsN p A d := by
  obtain ⟨hA, y, hyA, hyK, hyp, hyA'⟩ := h
  obtain ⟨T, hT1, hT2, hTK⟩ := hT
  have hCN : Subgroup.centralizer (stdLayer d : Set G₀) ≤ Subgroup.normalizer (T : Set G₀) :=
    (Subgroup.centralizer_le (show (T : Set G₀) ⊆ (stdLayer d : Set G₀) from fun t ht => hTK ht)).trans
      (Subgroup.centralizer_le_normalizer (T : Set G₀))
  refine ⟨⟨T, hT1, hT2, hTK, le_antisymm ?_ (sup_le inf_le_left inf_le_left)⟩, y, hyA, hyK, hyp, hyA'⟩
  calc A = (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.centralizer (stdLayer d : Set G₀)) := hA
    _ ≤ (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.normalizer (T : Set G₀)) :=
        sup_le_sup_left (inf_le_inf_left A hCN) _


private lemma mem_normalizer_stdLayer_of_mem_centralizer {G₀ : Type} [Group G₀] {d g : G₀}
    (hg : g ∈ Subgroup.centralizer ({d} : Set G₀)) :
    g ∈ Subgroup.normalizer (stdLayer d : Set G₀) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hgd : g * d = d * g := (Subgroup.mem_centralizer_iff.1 hg d (Set.mem_singleton d)).symm
  have hconj : (MulAut.conj g) d = d := by
    rw [MulAut.conj_apply, hgd, mul_assoc, mul_inv_cancel, mul_one]
  calc (stdLayer d).map (MulAut.conj g).toMonoidHom
      = (GLALayer (Subgroup.centralizer ({d} : Set G₀))).map (MulAut.conj g).toMonoidHom := rfl
    _ = GLALayer ((Subgroup.centralizer ({d} : Set G₀)).map (MulAut.conj g).toMonoidHom) :=
        (Y10F.glaLayer_map (ι := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective _).symm
    _ = GLALayer (Subgroup.centralizer ({d} : Set G₀)) := by
        rw [CFSG.centralizer_singleton_map, hconj]
    _ = stdLayer d := rfl

theorem ModelFactV.modelFactO {p : ℕ} {G₀ : Type} [Group G₀] [Finite G₀]
    (h : ModelFactV p G₀) : ModelFactO p G₀ :=
  fun A d hA hd => Or.inl (h A d hA hd)

private lemma isElemAbelian_sup_zpowers_and_centralizes {p : ℕ} {G₀ : Type} [Group G₀]
    {A : Subgroup G₀} (hA : IsElemAbelian p A) {d y : G₀} (hd : d ∈ A)
    (hyA : y ∈ Subgroup.centralizer (A : Set G₀)) (hyp : y ^ p = 1) :
    IsElemAbelian p (A ⊔ Subgroup.zpowers y) ∧
      A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({d} : Set G₀) := by
  constructor
  · exact hA.sup_of_commute (isElemAbelian_zpowers hyp) (fun a ha b hb => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((show Commute a y from Subgroup.mem_centralizer_iff.1 hyA a ha).zpow_right n).eq)
  · refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact (isElemAbelian_commute hA ha hd).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact Subgroup.mem_centralizer_iff.1 hyA d hd

private lemma le_normalizer_stdLayer_of_le_centralizer {G₀ : Type} [Group G₀]
    {A : Subgroup G₀} {d : G₀} (h : A ≤ Subgroup.centralizer ({d} : Set G₀)) :
    A ≤ Subgroup.normalizer (stdLayer d : Set G₀) :=
  fun _ ha => mem_normalizer_stdLayer_of_mem_centralizer (h ha)

private lemma sup_zpowers_split {G₀ : Type} [Group G₀] {A Kbar NT : Subgroup G₀} {y : G₀}
    (hAsplit : A = (A ⊓ Kbar) ⊔ (A ⊓ NT)) (hyNT : y ∈ NT) :
    A ⊔ Subgroup.zpowers y = ((A ⊔ Subgroup.zpowers y) ⊓ Kbar) ⊔
      ((A ⊔ Subgroup.zpowers y) ⊓ NT) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  refine sup_le ?_ ?_
  · calc A = (A ⊓ Kbar) ⊔ (A ⊓ NT) := hAsplit
      _ ≤ ((A ⊔ Subgroup.zpowers y) ⊓ Kbar) ⊔ ((A ⊔ Subgroup.zpowers y) ⊓ NT) :=
          sup_le ((inf_le_inf_right _ le_sup_left).trans le_sup_left)
            ((inf_le_inf_right _ le_sup_left).trans le_sup_right)
  · exact (le_inf le_sup_right (Subgroup.zpowers_le.2 hyNT)).trans le_sup_right

private lemma mem_normalizer_of_perfect_piImg {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {K : Subgroup Ω} (hKS : K ≤ S)
    (hK : Group.IsPerfect ↥K) {s : ↥S}
    (hs : M.π s ∈ Subgroup.normalizer (piImg M K : Set G₀)) :
    (s : Ω) ∈ Subgroup.normalizer (K : Set Ω) := by
  have hKsub : Group.IsPerfect ↥(K.subgroupOf S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKS).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKS).symm.surjective
  let H : Subgroup ↥S := (K.subgroupOf S).map (MulAut.conj s).toMonoidHom
  haveI : Group.IsPerfect ↥(K.subgroupOf S) := hKsub
  have hHperf : Group.IsPerfect ↥H := Group.IsPerfect.map (MulAut.conj s).toMonoidHom
  have hHle : H ≤ K.subgroupOf S ⊔ Subgroup.center ↥S := by
    rintro _ ⟨k, hk, rfl⟩
    have hkbar : M.π k ∈ piImg M K := Subgroup.mem_map_of_mem M.π hk
    have hconjbar : M.π ((MulAut.conj s) k) ∈ piImg M K := by
      have heq : M.π ((MulAut.conj s) k) = M.π s * M.π k * (M.π s)⁻¹ := by
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.1 hs (M.π k)).1 hkbar
    obtain ⟨k', hk', hk'pi⟩ := Subgroup.mem_map.1 hconjbar
    have hz : (k')⁻¹ * (MulAut.conj s) k ∈ Subgroup.center ↥S := by
      rw [← M.ker_π, MonoidHom.mem_ker, map_mul, map_inv, hk'pi, inv_mul_cancel]
    have heq : (MulAut.conj s) k = k' * ((k')⁻¹ * (MulAut.conj s) k) := by group
    rw [show (MulEquiv.toMonoidHom (MulAut.conj s)) k = (MulAut.conj s) k from rfl, heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right hz)
  have hHleK : H ≤ K.subgroupOf S :=
    CFSG.le_of_perfect_of_le_sup_center (Subgroup.isPerfect_iff.mp hKsub)
      (Subgroup.isPerfect_iff.mp hHperf) hHle
  have hHcard : Nat.card H = Nat.card (K.subgroupOf S) := by
    dsimp [H]
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
  have hHeq : H = K.subgroupOf S :=
    Subgroup.eq_of_le_of_card_ge hHleK (by rw [hHcard])
  have hHmap : H.map S.subtype = K.map (MulAut.conj (s : Ω)).toMonoidHom := by
    dsimp [H]
    have hcomp : S.subtype.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (s : Ω)).toMonoidHom.comp S.subtype := by
      apply MonoidHom.ext
      intro x
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map]
    calc (K.subgroupOf S).map (S.subtype.comp (MulAut.conj s).toMonoidHom)
        = (K.subgroupOf S).map ((MulAut.conj (s : Ω)).toMonoidHom.comp S.subtype) := by rw [hcomp]
      _ = ((K.subgroupOf S).map S.subtype).map (MulAut.conj (s : Ω)).toMonoidHom :=
          (Subgroup.map_map (K := K.subgroupOf S) (g := (MulAut.conj (s : Ω)).toMonoidHom)
            (f := S.subtype)).symm
      _ = K.map (MulAut.conj (s : Ω)).toMonoidHom := by rw [Subgroup.map_subgroupOf_eq_of_le hKS]
  have hmapK : K.map (MulAut.conj (s : Ω)).toMonoidHom = K := by
    have h := congrArg (Subgroup.map S.subtype) hHeq
    rw [hHmap, Subgroup.map_subgroupOf_eq_of_le hKS] at h
    exact h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hmapK

private lemma exists_B'_of_sup_zpowers {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} {G₀ : Type} [Group G₀] (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {y : G₀}
    (hEab : IsElemAbelian p (M.β.range ⊔ Subgroup.zpowers y)) (hyA' : y ∉ M.β.range) :
    ∃ P' B' : Subgroup Ω, P' ≤ S ∧ IsElemAbelian p P' ∧
      piImg M P' = M.β.range ⊔ Subgroup.zpowers y ∧
      Nat.card P' = Nat.card ↥(M.β.range ⊔ Subgroup.zpowers y) ∧
      IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ B' = Subgroup.zpowers x ⊔ P' := by
  obtain ⟨P', hP'S, hP'el, hP'E, hP'card, hP'max⟩ := exists_pLift hcfg M hZ hEab
  have hBS : B ⊓ S ≤ P' := by
    refine hP'max (B ⊓ S) inf_le_right (hcfg.elem.mono inf_le_left).isPGroup ?_
    exact (piImg_inf_S_le_range_β M).trans le_sup_left
  have hBB' : B ≤ Subgroup.zpowers x ⊔ P' := by
    rw [eq_zpowers_sup_inf hcfg M hZ]
    exact sup_le le_sup_left (hBS.trans le_sup_right)
  have hB'le : Subgroup.zpowers x ⊔ P' ≤ S ⊔ B :=
    sup_le ((Subgroup.zpowers_le.2 hcfg.mem).trans le_sup_right) (hP'S.trans le_sup_left)
  have hB'el : IsElemAbelian p (Subgroup.zpowers x ⊔ P') :=
    isElemAbelian_zpowers_sup_of_le_S hcfg hP'S hP'el
  have hBne : B ≠ Subgroup.zpowers x ⊔ P' := by
    intro hB'
    have hP'B : P' ≤ B := by rw [hB']; exact le_sup_right
    have hP'BS : P' ≤ B ⊓ S := le_inf hP'B hP'S
    have hmono : piImg M P' ≤ piImg M (B ⊓ S) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono S hP'BS)
    have hyE : y ∈ piImg M P' := by
      rw [hP'E]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    exact hyA' ((hmono.trans (piImg_inf_S_le_range_β M)) hyE)
  exact ⟨P', Subgroup.zpowers x ⊔ P', hP'S, hP'el, hP'E, hP'card, hB'el, hB'le, hBB', hBne, rfl⟩

private lemma split_P'_of_sup_zpowers {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B K : Subgroup Ω} {G₀ : Type} [Group G₀]
    (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    {P' U : Subgroup Ω} {A' Kbar NT : Subgroup G₀}
    (hP'S : P' ≤ S) (hP'el : IsElemAbelian p P') (hP'E : piImg M P' = A')
    (hP'card : Nat.card P' = Nat.card A') (hA'el : IsElemAbelian p A')
    (hA'split : A' = (A' ⊓ Kbar) ⊔ (A' ⊓ NT))
    (hKS : K ≤ S) (hd : piImg M K = Kbar) (hp : p.Prime)
    (hP'normU : ∀ q (hq : q ∈ P'), M.π ⟨q, hP'S hq⟩ ∈ NT →
      q ∈ Subgroup.normalizer (U : Set Ω)) :
    P' = (P' ⊓ K) ⊔ (P' ⊓ Subgroup.normalizer (U : Set Ω)) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro q hqP
  have hqS : q ∈ S := hP'S hqP
  have hqE : M.π ⟨q, hqS⟩ ∈ A' := by rw [← hP'E]; exact Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.2 hqP)
  rw [hA'split] at hqE
  obtain ⟨k, hk, n, hn, hkn⟩ :=
    (CFSG.mem_sup_of_commute (fun a ha b hb =>
      isElemAbelian_commute hA'el (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)).1 hqE
  have hkE : k ∈ piImg M P' := by rw [hP'E]; exact hk.1
  obtain ⟨r, hrP', hrk⟩ := Subgroup.mem_map.1 hkE
  have hnE : n ∈ piImg M P' := by rw [hP'E]; exact hn.1
  obtain ⟨s, hsP', hsn⟩ := Subgroup.mem_map.1 hnE
  have hprodπ : M.π ⟨q, hqS⟩ = M.π (r * s) := by
    rw [map_mul, hrk, hsn, ← hkn]
  have hdiff : ⟨q, hqS⟩ * (r * s)⁻¹ ∈ P'.subgroupOf S ⊓ M.π.ker := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (P'.subgroupOf S).mul_mem (Subgroup.mem_subgroupOf.2 hqP)
        ((P'.subgroupOf S).inv_mem ((P'.subgroupOf S).mul_mem hrP' hsP'))
    · exact MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hprodπ, mul_inv_cancel])
  have hone : ⟨q, hqS⟩ * (r * s)⁻¹ = 1 := by
    have h := hdiff
    rw [piImg_inf_ker_eq_bot M hP'S hP'E hP'card] at h
    exact Subgroup.mem_bot.1 h
  have hqeq : ⟨q, hqS⟩ = r * s := mul_inv_eq_one.1 hone
  have hqΩ : q = (r : Ω) * (s : Ω) := congrArg Subtype.val hqeq
  have hrK : (r : Ω) ∈ K :=
    mem_of_piImg_of_pow_eq_one M hKS hp hZ (by rw [hrk, hd]; exact hk.2)
      (by
        apply Subtype.ext
        simpa using hP'el.2 (r : Ω) (Subgroup.mem_subgroupOf.1 hrP'))
  have hsN : (s : Ω) ∈ Subgroup.normalizer (U : Set Ω) :=
    hP'normU (s : Ω) (Subgroup.mem_subgroupOf.1 hsP') (by rw [hsn]; exact hn.2)
  rw [hqΩ]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hrP', hrK⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hsP', hsN⟩))

private lemma split_B'_of_split {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x) {P' U : Subgroup Ω}
    (hP'S : P' ≤ S) (hP'el : IsElemAbelian p P')
    (hP'split : P' = (P' ⊓ K) ⊔ (P' ⊓ Subgroup.normalizer (U : Set Ω))) (hUK : U ≤ K) :
    Subgroup.zpowers x ⊔ P' = ((Subgroup.zpowers x ⊔ P') ⊓ K) ⊔
      ((Subgroup.zpowers x ⊔ P') ⊓ Subgroup.normalizer (U : Set Ω)) := by
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hxP : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ P', Commute a b := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxb : Commute x b := (Subgroup.mem_centralizer_iff.1 hxc b (hP'S hb)).symm
    exact hxb.zpow_left n
  intro b hb
  obtain ⟨z, hz, q, hqP, hzq⟩ := (CFSG.mem_sup_of_commute hxP).1 hb
  have hq_split : q ∈ (P' ⊓ K) ⊔ (P' ⊓ Subgroup.normalizer (U : Set Ω)) := by
    rw [← hP'split]; exact hqP
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    (CFSG.mem_sup_of_commute (fun a ha b hb =>
      isElemAbelian_commute hP'el (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)).1 hq_split
  have hzN : z ∈ Subgroup.normalizer (U : Set Ω) := by
    have hUS : (U : Set Ω) ⊆ (S : Set Ω) := fun u hu => (hUK.trans hKS) hu
    have hxN : x ∈ Subgroup.normalizer (U : Set Ω) :=
      ((Subgroup.zpowers_le.2 hxc).trans
        ((Subgroup.centralizer_le hUS).trans (Subgroup.centralizer_le_normalizer (U : Set Ω))))
        (Subgroup.mem_zpowers x)
    exact Subgroup.zpowers_le.2 hxN hz
  have hzr : z * (r : Ω) = (r : Ω) * z := (hxP z hz (r : Ω) hr.1).eq
  have hb_eq : b = (r : Ω) * (z * (s : Ω)) := by
    rw [← hzq, ← hrs, ← mul_assoc, hzr, mul_assoc]
  rw [hb_eq]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right hr.1, hr.2⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.2
      ⟨(Subgroup.zpowers x ⊔ P').mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hs.1),
        (Subgroup.normalizer (U : Set Ω)).mul_mem hzN hs.2⟩))

theorem exists_alt_iv_of_modelN {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    {G₀ : Type} [Group G₀] (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {d : G₀} (hd : piImg M K = stdLayer d)
    (hdmem : d ∈ M.β.range) (hext : StdExtendsN p M.β.range d) :
    ∃ B' U : Subgroup Ω, IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧
      B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Ω)) := by
  obtain ⟨⟨T, hT1, hT2, hTK, hAsplit⟩, y, hyA, hyK, hyp, hyA'⟩ := hext
  have hp := hcfg.prime
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  obtain ⟨hEab, hA'C⟩ :=
    isElemAbelian_sup_zpowers_and_centralizes (M.isElemAbelian_range_β hcfg.elem) hdmem hyA hyp
  have hAnormK := le_normalizer_stdLayer_of_le_centralizer hA'C
  obtain ⟨P', B', hP'S, hP'el, hP'E, hP'card, hB'el, hB'le, hBB', hBne, hB'def⟩ :=
    exists_B'_of_sup_zpowers hcfg M hZ hEab hyA'
  have hP'_normK : ∀ q ∈ P', q ∈ Subgroup.normalizer (K : Set Ω) := by
    intro q hqP
    have hqS : q ∈ S := hP'S hqP
    have hqbar : M.π ⟨q, hqS⟩ ∈ Subgroup.normalizer (piImg M K : Set G₀) := by
      rw [hd]
      exact hAnormK (by
        rw [← hP'E]
        exact Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.2 hqP))
    exact mem_normalizer_of_perfect_piImg M hKS (isPerfect_K hcfg) hqbar
  have hTle : T ≤ piImg M K := by rw [hd]; exact hTK
  obtain ⟨U, hUK, hU1, hU2, hUpi, hUnorm⟩ :=
    exists_twoCore_preimage_lift M hKS hTle hT2 hT1
  have hP'_normU : ∀ q (hq : q ∈ P'), M.π ⟨q, hP'S hq⟩ ∈ Subgroup.normalizer (T : Set G₀) →
      q ∈ Subgroup.normalizer (U : Set Ω) :=
    fun q hq hqNT => hUnorm ⟨q, hP'S hq⟩ (hP'_normK q hq) hqNT
  have hyT : y ∈ Subgroup.normalizer (T : Set G₀) :=
    Subgroup.centralizer_le_normalizer (T : Set G₀)
      (Subgroup.centralizer_le (fun t ht => hTK ht) hyK)
  have hA'split := sup_zpowers_split (A := M.β.range) (Kbar := stdLayer d)
    (NT := Subgroup.normalizer (T : Set G₀)) hAsplit hyT
  have hP'split := split_P'_of_sup_zpowers M hZ hP'S hP'el hP'E hP'card hEab hA'split hKS hd hp hP'_normU
  have hB'split := split_B'_of_split hcfg hP'S hP'el hP'split hUK
  refine ⟨B', U, hB'el, hB'le, hBB', hBne, hU1, hU2, hUK, ?_⟩
  rw [hB'def]
  exact hB'split

theorem concl_of_modelFactO {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {G₀ : Type} [Group G₀] [Finite G₀] (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) (h : ModelFactO p G₀) :
    T173Concl p S B K N := by
  obtain ⟨d, hdstd, -, hKd⟩ := exists_std_elt hcfg M hcfg.std
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  have hbmax : GLAIsBmax p M.β.range := isBmax_range hcfg M hZ
  have hlow : innerClosure M.β.range d ≤ piImg M (closureIn K N) := innerClosure_le_piImg hcfg M hZ hKd
  unfold T173Concl
  rcases h _ d hbmax hdstd with hV | hE
  · exfalso
    obtain ⟨T', hT'1, hT'2, hT'N⟩ := exists_two_subgroup_of_hc hcfg M
    exact hV ⟨T', hT'1, hT'2, (sup_le_sup_right hlow _).trans hT'N⟩
  · right
    exact exists_alt_iv_of_modelN hcfg M hZ hKd hdstd.1 hE


end CFSG.LocalAnalysis.GLTheoremA.T173O

end
