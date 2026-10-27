module

public import CFSG.GH74.Uniqueness.Section6AKey
public import CFSG.GH74.Uniqueness.Section6Cor64

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Section6A

variable {X : Type} [Group X]

theorem conjugate_le_conjugate {A B : Subgroup X} (hAB : A ≤ B) (g : X) :
    conjugate A g ≤ conjugate B g :=
  fun _ hx => mem_conjugate_iff.mpr (hAB (mem_conjugate_iff.mp hx))

end Section6A

section Prop63

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X}

@[expose] def oddHull (Z : Set X) (M : Subgroup X) : Subgroup X :=
  Subgroup.closure {x : X | x ∈ zHull Z M ∧ Odd (orderOf x)}

theorem oddHull_le_zHull (Z : Set X) (M : Subgroup X) : oddHull Z M ≤ zHull Z M :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem subset_oddHull {x : X} (hx : x ∈ zHull Z M) (hodd : Odd (orderOf x)) :
    x ∈ oddHull Z M :=
  Subgroup.subset_closure ⟨hx, hodd⟩

theorem le_normalizer_oddHull (hZ : IsInvariantInvolutionSet Z) (M : Subgroup X) :
    M ≤ normalizer (oddHull Z M : Set X) := by
  refine Section6A.le_normalizer_closure fun m hm x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_zHull hZ M hm) x).mp hx.1
  · have e : orderOf (m * x * m⁻¹) = orderOf x := by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective x
    rw [e]
    exact hx.2

theorem invertedSet_subset_oddHull (hZ : IsInvariantInvolutionSet Z) {z : X} {p : ℕ}
    {W : Subgroup X} (hW : T4Cand Z M z p W) {x : X}
    (hx : x ∈ CFSG.OddInversion.invertedSet W z) : x ∈ oddHull Z M := by
  have hz := hW.mem_Z
  have hzM := hW.mem_M
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hxW : x ∈ W := hx.1
  have hxM : x ∈ M := hW.le_M hxW
  have hodd : Odd (orderOf x) :=
    Section6A.odd_orderOf_of_isPGroup hW.prime hW.ne_two hW.pgroup hxW
  have hx' : z * x⁻¹ * z⁻¹ = x := by
    have e : z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
    rw [e, hx.2, inv_inv]
  have hxx : x * x = z * (x⁻¹ * z * x) := by
    calc x * x = (z * x⁻¹ * z⁻¹) * x := by rw [hx']
      _ = z * (x⁻¹ * z⁻¹ * x) := by group
      _ = z * (x⁻¹ * z * x) := by rw [hzi]
  have hmem : x * x ∈ zHull Z M := by
    rw [hxx]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hz, hzM⟩)
      (Subgroup.subset_closure ⟨hZ.2 z hz x, M.mul_mem (M.mul_mem (M.inv_mem hxM) hzM) hxM⟩)
  exact subset_oddHull (mem_of_mul_self_mem_of_odd_orderOf hodd hmem) hodd

variable [Finite X]

theorem oddHull_ne_bot (hZ : IsInvariantInvolutionSet Z) {z : X} {p : ℕ} {W : Subgroup X}
    (hW : T4Cand Z M z p W) : oddHull Z M ≠ ⊥ := by
  intro hbot
  apply hW.ne_bot
  rw [← hW.closure_invertedSet hZ, eq_bot_iff, Subgroup.closure_le]
  intro k hk
  have h1 := invertedSet_subset_oddHull hZ hW hk
  rw [hbot, Subgroup.mem_bot] at h1
  exact SetLike.mem_coe.mpr (Subgroup.mem_bot.mpr h1)

theorem ZDSetup.pPrimeCoreIn_lSubgroup_le (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    {t : X} (ht : t ∈ Z) (htM : t ∉ M) (hrank : 2 ≤ Open.pRank 2 (lSubgroup M z t)) :
    pPrimeCoreIn (lSubgroup M z t) ≤ pPrimeCoreIn (M ⊓ conjugate M t) := by
  have hZ := S.invariant
  have h := S.prodDisc
  set L : Subgroup X := lSubgroup M z t with hL
  set D : Subgroup X := M ⊓ conjugate M t with hD
  have hzL : z ∈ L := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have htL : t ∈ L := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hLO : L ≤ normalizer ((pPrimeCoreIn L : Subgroup X) : Set X) := pPrimeCoreIn_normalizes L
  have hzLL : zHull Z L = L := IsProductDisconnected.zHull_lSubgroup hZ ht hz M
  have hrank' : 2 ≤ Open.pRank 2
      (zHull Z (normalizer ((pPrimeCoreIn L : Subgroup X) : Set X))) := by
    refine hrank.trans (CFSG.SectionRank.pRank_mono Nat.one_lt_two ?_)
    calc L = zHull Z L := hzLL.symm
      _ ≤ zHull Z (normalizer ((pPrimeCoreIn L : Subgroup X) : Set X)) :=
        Subgroup.closure_mono (Set.inter_subset_inter_right Z (fun x hx => hLO hx))
  have hOM : pPrimeCoreIn L ≤ M :=
    S.lemma313 (odd_card_pPrimeCoreIn L) hrank' hz (hLO hzL) (self_mem_omega M)
      ((h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM)
  have htO : t ∈ normalizer ((pPrimeCoreIn L : Subgroup X) : Set X) := hLO htL
  have hOD : pPrimeCoreIn L ≤ D := by
    refine le_inf hOM fun x hx => ?_
    rw [mem_conjugate_iff]
    exact hOM ((Subgroup.mem_normalizer_iff.mp htO x).mp hx)
  have hDL : D ≤ normalizer ((pPrimeCoreIn L : Subgroup X) : Set X) := fun d hd =>
    mem_normalizer_pPrimeCoreIn (h.le_normalizer_lSubgroup hZ ht htM hz hzM hd)
  exact le_pPrimeCoreIn hOD hDL (odd_card_pPrimeCoreIn L)

theorem ZDSetup.exists_xdata_of_pRank (S : ZDSetup X Z M) {H : Subgroup X} (hH : H ≠ ⊤)
    (hHM : ¬ H ≤ M) (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hrank : 2 ≤ Open.pRank 2 (zHull Z H)) :
    ∃ u : X, XData Z M (zHull Z H) ((commutator ↥(zHull Z H)).map (zHull Z H).subtype)
      ((pPrimeCore 2 ↥(zHull Z H)).map (zHull Z H).subtype) u := by
  have hIH := S.zdConclusion_zHull hH hHM hne
  rw [zdConclusion_iff] at hIH
  rcases hIH with hr | ⟨u, hu⟩
  · exfalso
    have h2 : Open.twoRank ↥(zHull Z H) = Open.pRank 2 (zHull Z H) :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (zHull Z H)).symm
    omega
  · exact ⟨(u : X), hu.toXData⟩

theorem ZDSetup.not_doublyTransitive_of_normal_subgroup
    (S : ZDSetup X Z M) {β Y : Subgroup X}
    (hβΩ : β ∈ omega M) (hβM : β ≠ M) (hYM : Y ≤ M) (hYβ : Y ≤ β)
    (hYn : M ≤ normalizer (Y : Set X)) (hY1 : Y ≠ ⊥) : ¬ DoublyTransitive M := by
  intro hD
  have h := S.prodDisc
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  have hall : ∀ g : X, Y ≤ conjugate M g := by
    intro g
    by_cases hg : conjugate M g = M
    · rw [hg]
      exact hYM
    · obtain ⟨m, hmM, hm⟩ := h.exists_mem_conjugate_of_doublyTransitive hD hβΩ
        (conjugate_mem_omega (self_mem_omega M) g) hβM hg
      have hYm : conjugate Y m = Y := conjugate_eq_iff_mem_normalizer.mpr (hYn hmM)
      calc Y = conjugate Y m := hYm.symm
        _ ≤ conjugate β m := Section6A.conjugate_le_conjugate hYβ m
        _ = conjugate M g := hm
  have hcore : Y ≤ M.normalCore := by
    intro y hy
    show ∀ b : X, b * y * b⁻¹ ∈ M
    exact fun b => mem_conjugate_iff.mp (hall b hy)
  rcases hsimple.eq_bot_or_eq_top_of_normal M.normalCore with hbot | htop
  · rw [hbot] at hcore
    exact hY1 (le_bot_iff.mp hcore)
  · exact h.ne_top (top_unique (htop ▸ Subgroup.normalCore_le M))

theorem ZDSetup.exists_isSylowOf_normalizes_sup (S : ZDSetup X Z M) (hT2 : Theorem2Stmt Z M)
    (hnotDT : ¬ DoublyTransitive M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {t : X} (ht : t ∈ Z)
    (htM : t ∉ M) {q : ℕ} (hq : q.Prime)
    (hqO : q ∣ Nat.card (pPrimeCoreIn (M ⊓ conjugate M t))) :
    ∃ P : Subgroup X, ABGLocalTools.IsSylowOf q P (pPrimeCoreIn (M ⊓ conjugate M t)) ∧
      z ∈ normalizer ((oddHull Z M ⊔ P : Subgroup X) : Set X) := by
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact q.Prime := ⟨hq⟩
  set D : Subgroup X := M ⊓ conjugate M t with hD
  set K : Subgroup X := pPrimeCoreIn D with hK
  have hKodd : Odd (Nat.card K) := odd_card_pPrimeCoreIn D
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr hqO)
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hβΩ : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have hβM : conjugate M t ≠ M := fun heq =>
    htM ((h.conjugate_eq_iff_mem (self_mem_omega M)).mp heq)
  have hMnormY : M ≤ normalizer (oddHull Z M : Set X) := le_normalizer_oddHull hZ M
  obtain ⟨Pq, hPq⟩ := ABGLocalTools.exists_isSylowOf q K
  have hPqD : Pq ≤ D := hPq.le.trans (pPrimeCoreIn_le D)
  have hPqM : Pq ≤ M := hPqD.trans inf_le_left
  have hPqβ : Pq ≤ conjugate M t := hPqD.trans inf_le_right
  have h2 : 2 ≤ (omegaFix M (Pq : Set X)).ncard := by
    have hsub : ({M, conjugate M t} : Set (Subgroup X)) ⊆ omegaFix M (Pq : Set X) := by
      intro γ hγ
      rcases hγ with rfl | rfl
      · exact h.self_mem_omegaFix_iff.mpr hPqM
      · exact h.mem_omegaFix_iff.mpr ⟨hβΩ, hPqβ⟩
    calc 2 = ({M, conjugate M t} : Set (Subgroup X)).ncard := (Set.ncard_pair hβM.symm).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  obtain ⟨R, -, hRmax⟩ := Finite.exists_le_maximal
    (p := fun R : Subgroup X => IsPGroup q R ∧ R ≤ M ∧ Pq ≤ R ∧
      2 ≤ (omegaFix M (R : Set X)).ncard) (a := Pq) ⟨hPq.isPGroup, hPqM, le_rfl, h2⟩
  have hRp : IsPGroup q R := hRmax.prop.1
  have hRM : R ≤ M := hRmax.prop.2.1
  have hPqR : Pq ≤ R := hRmax.prop.2.2.1
  have hR2 : 2 ≤ (omegaFix M (R : Set X)).ncard := hRmax.prop.2.2.2
  have hno : ¬ ∃ P : Subgroup X, IsPGroup q P ∧ (omegaFix M (P : Set X)).ncard = 2 :=
    fun hex => hnotDT ((hT2 q hq hq2).1 hex)
  have hR3 : 3 ≤ (omegaFix M (R : Set X)).ncard := by
    by_contra hlt
    exact hno ⟨R, hRp, by omega⟩
  have hmax3 : ∀ Q : Subgroup X, IsPGroup q Q → Q ≤ M → 3 ≤ (omegaFix M (Q : Set X)).ncard →
      R ≤ Q → Q = R := by
    intro Q hQp hQM hQ3 hRQ
    exact le_antisymm (hRmax.2 ⟨hQp, hQM, hPqR.trans hRQ, by omega⟩ hRQ) hRQ
  obtain ⟨-, hfix⟩ := (hT2 q hq hq2).2 hno M (self_mem_omega M) R hRp hRM hR3 hmax3
  obtain ⟨s, hsZ, hsN, hsM⟩ := hfix M (h.self_mem_omegaFix_iff.mpr hRM)
  have hsM' : s ∈ M := (h.conjugate_eq_iff_mem (self_mem_omega M)).mp hsM
  obtain ⟨i, hiI, his⟩ := ((h.prop36c hZ ht htM).1 z ⟨hz, hzM⟩).surjOn ⟨hsZ, hsM'⟩
  have hiK : i ∈ K := hiI.1
  have his' : i⁻¹ * z * i = s := his
  have hiM : i ∈ M := (Subgroup.mem_inf.mp (pPrimeCoreIn_le D hiK)).1
  have hP'syl : ABGLocalTools.IsSylowOf q (conjugate Pq i⁻¹) K :=
    isSylowOf_conjugate_of_mem hPq (K.inv_mem hiK)
  have hP'R' : conjugate Pq i⁻¹ ≤ conjugate R i⁻¹ := Section6A.conjugate_le_conjugate hPqR _
  have hR'M : conjugate R i⁻¹ ≤ M := by
    intro x hx
    have hx' : i⁻¹ * x * i⁻¹⁻¹ ∈ R := mem_conjugate_iff.mp hx
    have e : x = i * (i⁻¹ * x * i⁻¹⁻¹) * i⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hiM (hRM hx')) (M.inv_mem hiM)
  have hR'p : IsPGroup q (conjugate R i⁻¹) := hRp.map (MulAut.conj i⁻¹⁻¹).toMonoidHom
  have hzR' : z ∈ normalizer ((conjugate R i⁻¹ : Subgroup X) : Set X) := by
    rw [normalizer_conjugate, mem_conjugate_iff, inv_inv, his']
    exact hsN
  have hcomm : ∀ x ∈ conjugate R i⁻¹, z * x * z⁻¹ * x⁻¹ ∈ oddHull Z M := by
    intro x hx
    have hzx : z * x * z⁻¹ ∈ conjugate R i⁻¹ := (Subgroup.mem_normalizer_iff.mp hzR' x).mp hx
    have hc : z * x * z⁻¹ * x⁻¹ ∈ conjugate R i⁻¹ :=
      (conjugate R i⁻¹).mul_mem hzx ((conjugate R i⁻¹).inv_mem hx)
    have hodd : Odd (orderOf (z * x * z⁻¹ * x⁻¹)) :=
      Section6A.odd_orderOf_of_isPGroup hq hq2 hR'p hc
    have hxM : x ∈ M := hR'M hx
    have e : z * x * z⁻¹ * x⁻¹ = z * (x * z * x⁻¹) := by rw [hzi]; group
    have hmem : z * x * z⁻¹ * x⁻¹ ∈ zHull Z M := by
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hz, hzM⟩)
        (Subgroup.subset_closure ⟨?_, M.mul_mem (M.mul_mem hxM hzM) (M.inv_mem hxM)⟩)
      simpa using hZ.2 z hz x⁻¹
    exact subset_oddHull hmem hodd
  refine ⟨conjugate Pq i⁻¹, hP'syl, ?_⟩
  refine Section6A.mem_normalizer_sup_of_conj_mem hz2 (fun x hx => ?_) (fun x hx => ?_)
  · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hMnormY hzM) x).mp hx)
  · have hxR' : x ∈ conjugate R i⁻¹ := hP'R' hx
    have e : z * x * z⁻¹ = (z * x * z⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm x hxR')) (Subgroup.mem_sup_right hx)

theorem ZDSetup.prop63
    (S : ZDSetup X Z M) (hT2 : Theorem2Stmt Z M) : Prop63Stmt Z M := by
  intro z p W hW t ht htM hβ
  by_contra hLtop
  have hZ := S.invariant
  have h := S.prodDisc
  have hz := hW.mem_Z
  have hzM := hW.mem_M
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set L : Subgroup X := lSubgroup M z t with hLdef
  set D : Subgroup X := M ⊓ conjugate M t with hD
  set K : Subgroup X := pPrimeCoreIn D with hK
  have hzL : z ∈ L := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have htL : t ∈ L := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hLM : ¬ L ≤ M := fun hle => htM (hle htL)
  have hZML : Z ∩ (M : Set X) ⊆ (L : Set X) := h.inter_le_lSubgroup hZ ht htM hz hzM
  have hzLL : zHull Z L = L := IsProductDisconnected.zHull_lSubgroup hZ ht hz M
  have hMhull : zHull Z M ≤ L := (Subgroup.closure_le _).mpr hZML
  have hrankL : 2 ≤ Open.pRank 2 L :=
    (S.two_le_pRank_zHull hz hzM).trans (CFSG.SectionRank.pRank_mono Nat.one_lt_two hMhull)
  have hne : (Z ∩ ((L ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzL, hzM⟩⟩
  obtain ⟨u, hX⟩ := S.exists_xdata_of_pRank hLtop hLM hne (by rw [hzLL]; exact hrankL)
  rw [hzLL] at hX
  have hZL : ∀ y ∈ Z, y ∈ M → y ∈ L := fun y hy hyM => hZML ⟨hy, hyM⟩
  have hYO' : oddHull Z M ≤ pPrimeCoreIn L := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact hX.odd_mem_of_mem_zHull hZ hZL hx.1 hx.2
  have hOLD : pPrimeCoreIn L ≤ K := S.pPrimeCoreIn_lSubgroup_le hz hzM ht htM hrankL
  have hYK : oddHull Z M ≤ K := hYO'.trans hOLD
  have hYD : oddHull Z M ≤ D := hYK.trans (pPrimeCoreIn_le D)
  have hYM : oddHull Z M ≤ M := hYD.trans inf_le_left
  have hYβ : oddHull Z M ≤ conjugate M t := hYD.trans inf_le_right
  have hβΩ : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have hβM : conjugate M t ≠ M := fun heq =>
    htM ((h.conjugate_eq_iff_mem (self_mem_omega M)).mp heq)
  have hnotDT : ¬ DoublyTransitive M :=
    S.not_doublyTransitive_of_normal_subgroup hβΩ hβM hYM hYβ (le_normalizer_oddHull hZ M)
      (oddHull_ne_bot hZ hW)
  have hzK : z ∈ normalizer (K : Set X) :=
    Section6A.mem_normalizer_of_forall_isSylowOf hz2 hYK fun q hq hqO =>
      S.exists_isSylowOf_normalizes_sup hT2 hnotDT hz hzM ht htM hq hqO
  have hKodd : Odd (Nat.card K) := odd_card_pPrimeCoreIn D
  obtain ⟨y, hyZ, hyz, hyc⟩ := S.exists_commuting_ne hz
  have hyM : y ∈ M :=
    h.centralizer_le_of_mem hz hzM (Subgroup.mem_centralizer_singleton_iff.mpr hyc)
  obtain ⟨i, hiI, hiy⟩ := ((h.prop36c hZ ht htM).1 z ⟨hz, hzM⟩).surjOn ⟨hyZ, hyM⟩
  have hiK : i ∈ K := hiI.1
  have hiy' : i⁻¹ * z * i = y := hiy
  have hyzK : y * z ∈ K := by
    have hzk : z * i * z⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hzK i).mp hiK
    have e : y * z = i⁻¹ * (z * i * z⁻¹) := by rw [← hiy', hzi]; group
    rw [e]
    exact K.mul_mem (K.inv_mem hiK) hzk
  have hy2 : y * y = 1 := hZ.mul_self_eq_one hyZ
  have hyyz : (y * z) * (y * z) = 1 := by
    calc (y * z) * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hyc]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy2, hz2, one_mul]
  have hyz1 : y * z = 1 := eq_one_of_mem_of_sq_eq_one hKodd hyzK hyyz
  apply hyz
  rw [eq_inv_of_mul_eq_one_left hyz1, hzi]

theorem ZDSetup.cor64
    (S : ZDSetup X Z M) (hT2 : Theorem2Stmt Z M) : Cor64Stmt Z M :=
  S.cor64_of_prop63 (S.prop63 hT2)

end Prop63

end CFSG.GH74.Uniqueness
