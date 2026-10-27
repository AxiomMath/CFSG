module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U38SylowSound
public import Certificates.Certificate211003

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 U38Sylow
open CFSG.Yardstones.Md0ec50421ce4
open scoped Classical

theorem ys07_commAt_iff {a b : Array ℕ} (ha : validA 513 a = true) (hb : validA 513 b = true) :
    commAt a b = true ↔ permOfArr 513 a * permOfArr 513 b = permOfArr 513 b * permOfArr 513 a :=
  eqA_iff (rep_compA (rep_of_validA ha) (rep_of_validA hb)) (rep_compA (rep_of_validA hb) (rep_of_validA ha))

theorem ys07_cubeOne_iff {a : Array ℕ} (ha : validA 513 a = true) :
    cubeOne a = true ↔ permOfArr 513 a ^ 3 = 1 := by
  rw [pow_three]
  exact eqA_iff (rep_compA (rep_of_validA ha) (rep_compA (rep_of_validA ha) (rep_of_validA ha))) rep_idA

theorem ys07_index_inj {pts : Array (Array ℕ)} {Q : Subgroup (Equiv.Perm (Fin 513))}
    (hmem : ∀ x, x ∈ Q ↔ ∃ i < pts.size, permOfArr 513 pts[i]! = x) (hcard : Nat.card Q = pts.size)
    {i j : ℕ} (hi : i < pts.size) (hj : j < pts.size)
    (h : permOfArr 513 pts[i]! = permOfArr 513 pts[j]!) : i = j := by
  let F : Fin pts.size → Q := fun k => ⟨permOfArr 513 pts[k.1]!, (hmem _).2 ⟨k.1, k.2, rfl⟩⟩
  have hF : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, rfl⟩ := (hmem x).1 hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hb := hF.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard])
  exact congrArg Fin.val (hb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h))

theorem ys07_card_eq_filter (H : Subgroup (Equiv.Perm (Fin 513))) :
    Nat.card H = (Finset.univ.filter fun y => y ∈ H).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem ys07_mem_cenOf {pts : Array (Array ℕ)} {i j : ℕ} :
    j ∈ cenOf pts i ↔ j < pts.size ∧ commAt pts[i]! pts[j]! = true := by
  simp [cenOf, List.mem_filter, List.mem_range]

theorem ys07_card_cen {pts : Array (Array ℕ)} {Q : Subgroup (Equiv.Perm (Fin 513))}
    (hval : ∀ i < pts.size, validA 513 pts[i]! = true)
    (hmem : ∀ x, x ∈ Q ↔ ∃ i < pts.size, permOfArr 513 pts[i]! = x) (hcard : Nat.card Q = pts.size)
    {i : ℕ} (hi : i < pts.size) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({permOfArr 513 pts[i]!} : Set (Equiv.Perm (Fin 513)))) =
      (cenOf pts i).length := by
  classical
  have hnd : (cenOf pts i).Nodup := (List.nodup_range.filter _)
  rw [ys07_card_eq_filter, show (Finset.univ.filter fun y =>
      y ∈ Q ⊓ Subgroup.centralizer ({permOfArr 513 pts[i]!} : Set (Equiv.Perm (Fin 513)))) =
      (cenOf pts i).toFinset.image (fun j => permOfArr 513 pts[j]!) from ?_]
  · rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
    intro j hj k hk h
    simp only [Finset.coe_image, Set.mem_image, List.coe_toFinset, Set.mem_setOf_eq] at hj hk
    exact ys07_index_inj hmem hcard (ys07_mem_cenOf.1 hj).1 (ys07_mem_cenOf.1 hk).1 h
  · ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨hyQ, hyc⟩
      obtain ⟨j, hj, rfl⟩ := (hmem y).1 hyQ
      refine ⟨j, ys07_mem_cenOf.2 ⟨hj, (ys07_commAt_iff (hval i hi) (hval j hj)).2 hyc.symm⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjl, hc⟩ := ys07_mem_cenOf.1 hj
      exact ⟨(hmem _).2 ⟨j, hjl, rfl⟩, ((ys07_commAt_iff (hval i hi) (hval j hjl)).1 hc).symm⟩

theorem ys07_comm_of_elemAb {G : Type} [Group G] {E : Subgroup G} (hE : IsElemAbelian 3 E) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have := hE.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val this

set_option linter.constructorNameAsVariable false in
theorem ys07_elemAb_lt_81_of_pts {pts : Array (Array ℕ)} {Q : Subgroup (Equiv.Perm (Fin 513))}
    (hval : ∀ i < pts.size, validA 513 pts[i]! = true)
    (hmem : ∀ x, x ∈ Q ↔ ∃ i < pts.size, permOfArr 513 pts[i]! = x)
    (hcard : Nat.card Q = pts.size) (hQ : Nat.card Q = 729) (hck : noE81Pts pts = true)
    {E : Subgroup (Equiv.Perm (Fin 513))} (hEQ : E ≤ Q) (hE : IsElemAbelian 3 E) :
    Nat.card E < 81 := by
  classical
  set Ls : List ℕ := (List.range pts.size).filter fun i => cubeOne pts[i]! with hLs
  set bigL : List ℕ := Ls.filter fun i => 243 ≤ (cenOf pts i).length with hbigL
  have hbig : bigL.length ≤ 80 := by
    have h := hck
    simp only [noE81Pts, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl : ((Ls.map fun i => (i, cenOf pts i)).filter fun p => 243 ≤ p.2.length).length = bigL.length := by
      simp [hbigL, List.filter_map, Function.comp_def]
    rw [← hl]
    exact h.1
  have hnon : ∀ i ∈ Ls, (cenOf pts i).length = 81 → nonAbelianAt pts (cenOf pts i) = true := by
    intro i hi h81
    have h := hck
    simp only [noE81Pts, Bool.and_eq_true, List.all_eq_true] at h
    have hmemp := h.2 (i, cenOf pts i) (List.mem_map.2 ⟨i, hi, rfl⟩)
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true] at hmemp
    rcases hmemp with h' | h'
    · exact absurd h81 h'
    · exact h'
  have hmemLs : ∀ i, i ∈ Ls ↔ i < pts.size ∧ cubeOne pts[i]! = true := by
    intro i
    simp [hLs, List.mem_filter, List.mem_range]
  by_contra hlt
  push Not at hlt
  have hA : ∃ x ∈ E, Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 513)))) < 243 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ.filter fun y => y ∈ E) ⊆
        bigL.toFinset.image fun j => permOfArr 513 pts[j]! := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨i, hi, rfl⟩ := (hmem _).1 (hEQ hy)
      rw [Finset.mem_image]
      refine ⟨i, ?_, rfl⟩
      rw [List.mem_toFinset, hbigL, List.mem_filter]
      refine ⟨(hmemLs i).2 ⟨hi, (ys07_cubeOne_iff (hval i hi)).2 (hE.2 _ hy)⟩, ?_⟩
      have h := hall _ hy
      rw [ys07_card_cen hval hmem hcard hi] at h
      exact decide_eq_true h
    have hle : Nat.card E ≤ bigL.length := by
      rw [ys07_card_eq_filter]
      have h1 := Finset.card_le_card hsub
      have h2 : (bigL.toFinset.image fun j => permOfArr 513 pts[j]!).card ≤ bigL.length :=
        Finset.card_image_le.trans (List.toFinset_card_le _)
      exact h1.trans h2
    omega
  obtain ⟨x, hxE, hx243⟩ := hA
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 (hEQ hxE)
  set C : Subgroup (Equiv.Perm (Fin 513)) :=
    Q ⊓ Subgroup.centralizer ({permOfArr 513 pts[i]!} : Set (Equiv.Perm (Fin 513))) with hC
  have hEC : E ≤ C := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨hEQ hy, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (ys07_comm_of_elemAb hE hy hxE)
  have hCQ : C ≤ Q := inf_le_left
  have hdvd : Nat.card C ∣ 729 := hQ ▸ Subgroup.card_dvd_of_le hCQ
  rw [show (729 : ℕ) = 3 ^ 6 by norm_num] at hdvd
  obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hEC' : Nat.card E ≤ Nat.card C := Subgroup.card_le_of_le hEC
  have hC_lt : Nat.card C < 243 := hx243
  have hC_ge : 81 ≤ Nat.card C := hlt.trans hEC'
  have hC81 : Nat.card C = 81 := by
    rw [hCk] at hC_lt hC_ge ⊢
    interval_cases k <;> (try norm_num at hC_ge) <;> (try norm_num at hC_lt) <;> norm_num
  have hEeq : E = C := Subgroup.eq_of_le_of_card_ge hEC (by omega)
  have hlen : (cenOf pts i).length = 81 := by
    rw [← ys07_card_cen hval hmem hcard hi]
    exact hC81
  have hna := hnon i ((hmemLs i).2 ⟨hi, (ys07_cubeOne_iff (hval i hi)).2 (hE.2 _ hxE)⟩) hlen
  obtain ⟨j, hj, hna'⟩ := List.any_eq_true.1 hna
  obtain ⟨k', hk', hna''⟩ := List.any_eq_true.1 hna'
  have hfalse : commAt pts[j]! pts[k']! = false := by simpa using hna''
  have hjC : permOfArr 513 pts[j]! ∈ E := by
    rw [hEeq]
    obtain ⟨hjl, hc⟩ := ys07_mem_cenOf.1 hj
    refine Subgroup.mem_inf.2 ⟨(hmem _).2 ⟨j, hjl, rfl⟩, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 ((ys07_commAt_iff (hval i hi) (hval j hjl)).1 hc).symm
  have hkC : permOfArr 513 pts[k']! ∈ E := by
    rw [hEeq]
    obtain ⟨hkl, hc⟩ := ys07_mem_cenOf.1 hk'
    refine Subgroup.mem_inf.2 ⟨(hmem _).2 ⟨k', hkl, rfl⟩, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 ((ys07_commAt_iff (hval i hi) (hval k' hkl)).1 hc).symm
  have hcomm := ys07_comm_of_elemAb hE hjC hkC
  have htrue : commAt pts[j]! pts[k']! = true :=
    (ys07_commAt_iff (hval j (ys07_mem_cenOf.1 hj).1) (hval k' (ys07_mem_cenOf.1 hk').1)).2 hcomm
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem ys07_elemAb_le_27_of_pts {pts : Array (Array ℕ)} {Q : Subgroup (Equiv.Perm (Fin 513))}
    (hval : ∀ i < pts.size, validA 513 pts[i]! = true)
    (hmem : ∀ x, x ∈ Q ↔ ∃ i < pts.size, permOfArr 513 pts[i]! = x)
    (hcard : Nat.card Q = pts.size) (hQ : Nat.card Q = 729) (hck : noE81Pts pts = true)
    {E : Subgroup (Equiv.Perm (Fin 513))} (hEQ : E ≤ Q) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  have h81 := ys07_elemAb_lt_81_of_pts hval hmem hcard hQ hck hEQ hE
  have hdvd : Nat.card E ∣ 729 := hQ ▸ Subgroup.card_dvd_of_le hEQ
  rw [show (729 : ℕ) = 3 ^ 6 by norm_num] at hdvd
  obtain ⟨k, hk, hEk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hEk] at h81 ⊢
  interval_cases k <;> (try norm_num at h81) <;> norm_num

theorem u38_elemAb_le_27
    (E : Subgroup U38G) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  classical
  have h : u38NoE81Check () = true := Certificates.certificate211003
  have h' : u38SylowCheck () && noE81Check () = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨h1, h2⟩ := h'
  have hck : noE81Pts (qCert ()).pts = true := h2
  have hu := h1
  simp only [u38SylowCheck, Bool.and_eq_true, beq_iff_eq] at hu
  obtain ⟨⟨⟨⟨henum, hsize⟩, hsift⟩, -⟩, -⟩ := hu
  have hps : ∀ p ∈ keyPts, p < 513 := by
    intro p hp
    simp [keyPts, base1, base1L] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hQ : Nat.card U38Q = 729 := by
    change Nat.card (Subgroup.closure (permsA 513 qGens)) = 729
    rw [hcard, hsize]
  have hQΓ : U38Q ≤ U38G := by
    rw [U38Q, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact mem_U38G_of_sift1 (enumOK_gens_valid henum hk) (allLt_spec hsift hk)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Qs : Subgroup U38G := U38Q.subgroupOf U38G
  have hQs : Nat.card Qs = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv, hQ]
    norm_num
  have hindex : ¬ 3 ∣ Qs.index := by
    have h1 := Subgroup.card_mul_index Qs
    rw [hQs, card_U38G] at h1
    have h2 : Qs.index = 136192 := by omega
    rw [h2]
    decide
  let Q₀ : Sylow 3 U38G := (IsPGroup.of_card hQs).toSylow hindex
  have hE3 : IsPGroup 3 E := fun y => ⟨1, by simpa using Subtype.ext (hE.2 (y : U38G) y.2)⟩
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U38G P Q₀
  have hconj : ∀ e ∈ E, g * e * g⁻¹ ∈ (Q₀ : Subgroup U38G) := by
    intro e he
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨e, hEP he, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  let E' : Subgroup U38G := E.map (MulAut.conj g).toMonoidHom
  have hE'Q : E'.map U38G.subtype ≤ U38Q := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, rfl⟩ := hx
    exact Subgroup.mem_subgroupOf.1 (hconj e he)
  have hE'ab : IsElemAbelian 3 (E'.map U38G.subtype) :=
    (hE.map (MulAut.conj g).toMonoidHom).map U38G.subtype
  have hcardE' : Nat.card (E'.map U38G.subtype) = Nat.card E := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective U38G),
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← hcardE']
  exact ys07_elemAb_le_27_of_pts hval hmem hcard hQ hck hE'Q hE'ab

theorem u38_aut_inj {S : Type} [Group S] [Finite S]
    (hcat : catalogIs S S9.isU3eight) :
    ∃ κ : MulAut S →* U38G, Function.Injective κ := by
  have hX : Nonempty (S ≃* ↥(CFSG.PGLModel.projSU 3 2 3)) := by
    obtain ⟨e⟩ := bridge_u3eight hcat
    have hP : CFSG.PGLModel.projImage (CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 6)) =
        CFSG.PGLModel.projSU 3 2 3 :=
      CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 2 3
    exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage _ hP)⟩
  obtain ⟨eX⟩ := nonempty_equiv_X' hX
  let ρ' : U38G ≃* MulAut X' := MulEquiv.ofBijective rhoU38 (rhoU38_bijective hX)
  exact ⟨ρ'.symm.toMonoidHom.comp (MulAut.congr eX).toMonoidHom,
    ρ'.symm.injective.comp (MulAut.congr eX).injective⟩

theorem aut_u38_le_27
    {S : Type} [Group S] [Finite S] (hcat : catalogIs S S9.isU3eight)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  obtain ⟨κ, hκ⟩ := u38_aut_inj hcat
  have h := u38_elemAb_le_27 (E.map κ) (hE.map κ)
  rwa [Subgroup.card_map_of_injective hκ] at h

end CFSG.LocalAnalysis.GLTheoremA.CatB
