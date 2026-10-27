module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternPiece
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched

public section

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (form gram gram_apply par sgn ofSymplecticBasis
  mat_ofSymplecticBasis_mulVec_single exists_symplectic_basis planeGroup_span_conj
  mem_center_of_conj_mem_center planeGroup IsHyperbolicPlane stdPlane longInv longBlock
  coords suppGroup mem_coords planeGroup_stdPlane eq_one_of_mem_center_of_mem_suppGroup
  longInv_mem_longRootSp2 longRootSp2_eq_suppGroup suppGroup_mono isLongRootSp2_standard
  longInv_ne_of_ne range_longBlock longBlock_injective commute_longRootSp2
  isPerfect_statedSp_of_four_le mem_center_of_forall_commutator_mem_center)
open CFSG.ClassicalInvolution.Balance.Theorem5 CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement Matrix

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

section Model

variable {F : Type} [Field F]

theorem longInv_mul_not_mem_center (h2 : (2 : F) ≠ 0) :
    longInv F 3 0 * longInv F 3 1 ∉ Subgroup.center (StatedSp 3 F) := by
  intro hc
  have hs : longInv F 3 0 * longInv F 3 1 ∈
      suppGroup (coords 0 ∪ coords 1 : Set (Fin 3 ⊕ Fin 3)) := by
    refine mul_mem ?_ ?_
    · have := longInv_mem_longRootSp2 (K := F) (n := 3) 0
      rw [longRootSp2_eq_suppGroup] at this
      exact suppGroup_mono Set.subset_union_left this
    · have := longInv_mem_longRootSp2 (K := F) (n := 3) 1
      rw [longRootSp2_eq_suppGroup] at this
      exact suppGroup_mono Set.subset_union_right this
  have h1 := eq_one_of_mem_center_of_mem_suppGroup hc hs (t := Sum.inl (2 : Fin 3)) (by
    simp only [Set.mem_union, mem_coords, not_or]
    decide)
  have hsq : longInv F 3 1 * longInv F 3 1 = 1 :=
    (isLongRootSp2_standard (K := F) (n := 3) 1).mul_self h2
  have : longInv F 3 0 = longInv F 3 1 := by
    calc longInv F 3 0 = longInv F 3 0 * (longInv F 3 1 * longInv F 3 1) := by rw [hsq, mul_one]
      _ = (longInv F 3 0 * longInv F 3 1) * longInv F 3 1 := by rw [mul_assoc]
      _ = longInv F 3 1 := by rw [h1, one_mul]
  exact longInv_ne_of_ne h2 (by decide : (0 : Fin 3) ≠ 1) this

theorem hom_longInv_eq_of_mem {X : Type} [Group X] (h2 : (2 : F) ≠ 0) (φ : StatedSp 3 F →* X)
    (hker : φ.ker ≤ Subgroup.center (StatedSp 3 F)) {k l : Fin 3} (hkl : l ≠ k) {x : X}
    (hx : x ∈ (planeGroup (stdPlane F 3 k)).map φ) (hord : orderOf x = 2) :
    φ (longInv F 3 k) = x := by
  rw [planeGroup_stdPlane] at hx
  obtain ⟨a, ⟨s, rfl⟩, rfl⟩ := hx
  have hsq : φ (longBlock F 3 k (s * s)) = 1 := by
    rw [map_mul, map_mul]
    show φ (longBlock F 3 k s) * φ (longBlock F 3 k s) = 1
    rw [← pow_two]
    have := pow_orderOf_eq_one (φ (longBlock F 3 k s))
    rwa [hord] at this
  have hc : longBlock F 3 k (s * s) ∈ Subgroup.center (StatedSp 3 F) :=
    hker (MonoidHom.mem_ker.mpr hsq)
  have hs : longBlock F 3 k (s * s) ∈ suppGroup (coords k : Set (Fin 3 ⊕ Fin 3)) := by
    rw [← range_longBlock]
    exact ⟨_, rfl⟩
  have h1 := eq_one_of_mem_center_of_mem_suppGroup hc hs (t := Sum.inl l) (by
    rw [mem_coords]
    rintro (h | h)
    · exact hkl (Sum.inl_injective h)
    · cases h)
  have hss : s * s = 1 := by
    apply longBlock_injective k
    rw [h1, map_one]
  rcases sl2_sq_eq_one h2 hss with h | h
  · exfalso
    subst h
    rw [map_one, map_one, orderOf_one] at hord
    omega
  · subst h
    rfl

theorem exists_symplectic_basis_three (u v : Fin 3 ⊕ Fin 3 → F) (h : form u v = 1) :
    ∃ b : Module.Basis (Fin 3 ⊕ Fin 3) F (Fin 3 ⊕ Fin 3 → F),
      (∀ x y, form (b x) (b y) = gram F 3 x y) ∧ b (Sum.inl 0) = u ∧ b (Sum.inr 0) = v :=
  exists_symplectic_basis (m := 2) u v h

end Model

section Involutions

variable {G : Type} [Group G]

theorem mem_closure_insert_of_involution {S : Set G} {c : G} (hc : c * c = 1)
    (hcS : ∀ s ∈ S, c * s = s * c) {x : G} (hx : x ∈ Subgroup.closure (insert c S)) :
    x ∈ Subgroup.closure S ∨ ∃ g ∈ Subgroup.closure S, x = g * c := by
  set F : Subgroup G := Subgroup.closure S with hF
  have hFc : F ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hF, Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hcS s hs).symm
  have hcF : ∀ x ∈ F, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hFc hx)).symm
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact Or.inr ⟨1, F.one_mem, by simp⟩
    · exact Or.inl (Subgroup.subset_closure hy)
  | one => exact Or.inl F.one_mem
  | mul y w _ _ hy hw =>
    rcases hy with hy | ⟨g, hg, rfl⟩ <;> rcases hw with hw | ⟨g', hg', rfl⟩
    · exact Or.inl (F.mul_mem hy hw)
    · exact Or.inr ⟨y * g', F.mul_mem hy hg', by group⟩
    · refine Or.inr ⟨g * w, F.mul_mem hg hw, ?_⟩
      calc g * c * w = g * (c * w) := by group
        _ = g * (w * c) := by rw [hcF w hw]
        _ = g * w * c := by group
    · refine Or.inl ?_
      have e : g * c * (g' * c) = g * g' := by
        calc g * c * (g' * c) = g * (c * g') * c := by group
          _ = g * (g' * c) * c := by rw [hcF g' hg']
          _ = g * g' * (c * c) := by group
          _ = g * g' := by rw [hc]; group
      rw [e]
      exact F.mul_mem hg hg'
  | inv y _ hy =>
    rcases hy with hy | ⟨g, hg, rfl⟩
    · exact Or.inl (F.inv_mem hy)
    · refine Or.inr ⟨g⁻¹, F.inv_mem hg, ?_⟩
      have h1 : c * g⁻¹ = g⁻¹ * c := hcF g⁻¹ (F.inv_mem hg)
      calc (g * c)⁻¹ = c⁻¹ * g⁻¹ := by group
        _ = c * g⁻¹ := by rw [hcinv]
        _ = g⁻¹ * c := h1

theorem eq_one_or_eq_of_mem_closure_involution {c x : G} (hc : c * c = 1)
    (hx : x ∈ Subgroup.closure ({c} : Set G)) : x = 1 ∨ x = c := by
  rw [← insert_empty_eq] at hx
  rcases mem_closure_insert_of_involution hc (S := ∅)
    (fun s hs => absurd hs (Set.notMem_empty s)) hx with h | ⟨g, hg, rfl⟩
  · rw [Subgroup.closure_empty] at h
    exact Or.inl (Subgroup.mem_bot.mp h)
  · rw [Subgroup.closure_empty] at hg
    rw [Subgroup.mem_bot.mp hg, one_mul]
    exact Or.inr rfl

variable [Finite G]

theorem card_closure_insert_of_involution {S : Set G} {c : G} (hc : c * c = 1)
    (hcS : ∀ s ∈ S, c * s = s * c) (hnot : c ∉ Subgroup.closure S) :
    Nat.card (Subgroup.closure (insert c S)) = 2 * Nat.card (Subgroup.closure S) := by
  have hle := card_closure_insert_le hc hcS
  have hFA : Subgroup.closure S ≤ Subgroup.closure (insert c S) :=
    Subgroup.closure_mono (Set.subset_insert c S)
  have hdvd : Nat.card (Subgroup.closure S) ∣ Nat.card (Subgroup.closure (insert c S)) :=
    Subgroup.card_dvd_of_le hFA
  have hne : Nat.card (Subgroup.closure (insert c S)) ≠ Nat.card (Subgroup.closure S) := by
    intro h
    have heq : Subgroup.closure S = Subgroup.closure (insert c S) :=
      Subgroup.eq_of_le_of_card_ge hFA (by rw [h])
    exact hnot (heq ▸ Subgroup.subset_closure (Set.mem_insert c S))
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card (Subgroup.closure S) := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    have : 0 < Nat.card (Subgroup.closure (insert c S)) := Nat.card_pos
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne hk
  have hk3 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : Nat.card (Subgroup.closure S) * 3 ≤ Nat.card (Subgroup.closure S) * k :=
      Nat.mul_le_mul_left _ h
    omega
  have hk2 : k = 2 := by omega
  rw [hk, hk2, mul_comm]

theorem card_closure_three_involutions {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (habc : a ≠ b * c) : Nat.card (Subgroup.closure ({a, b, c} : Set G)) = 8 := by
  have c1 : Nat.card (Subgroup.closure ({c} : Set G)) = 2 := by
    have h := card_closure_insert_of_involution (S := (∅ : Set G)) hc
      (fun s hs => absurd hs (Set.notMem_empty s))
      (by rw [Subgroup.closure_empty, Subgroup.mem_bot]; exact hc1)
    rwa [insert_empty_eq, Subgroup.closure_empty, Subgroup.card_bot, mul_one] at h
  have hN1 : b ∉ Subgroup.closure ({c} : Set G) := by
    intro h
    rcases eq_one_or_eq_of_mem_closure_involution hc h with h1 | h1
    · exact hb1 h1
    · exact hbc' h1
  have hbS : ∀ s ∈ ({c} : Set G), b * s = s * b := by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact hbc
  have c2 : Nat.card (Subgroup.closure (insert b ({c} : Set G))) = 4 := by
    rw [card_closure_insert_of_involution hb hbS hN1, c1]
  have hN2 : a ∉ Subgroup.closure (insert b ({c} : Set G)) := by
    intro h
    rcases mem_closure_insert_of_involution hb hbS h with h1 | ⟨g, hg, hag⟩
    · rcases eq_one_or_eq_of_mem_closure_involution hc h1 with h2 | h2
      · exact ha1 h2
      · exact hac' h2
    · rcases eq_one_or_eq_of_mem_closure_involution hc hg with h2 | h2
      · rw [h2, one_mul] at hag
        exact hab' hag
      · rw [h2] at hag
        exact habc (hag.trans hbc.symm)
  have haS : ∀ s ∈ insert b ({c} : Set G), a * s = s * a := by
    rintro s (rfl | hs)
    · exact hab
    · rw [Set.mem_singleton_iff.mp hs]
      exact hac
  rw [card_closure_insert_of_involution ha haS hN2, c2]

end Involutions

section Triple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_twin_triple (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z) {M : Subgroup G} (hM : M ∈ Ω)
    {w : G} (hw : IsClassicalMember p f M w) (hMK : M ≠ K) (hKM : Commutes K M) :
    ∃ (M' : Subgroup G) (w' : G), M' ∈ Ω ∧ IsClassicalMember p f M' w' ∧ M' ≠ K ∧
      Commutes K M' ∧ Commutes M M' ∧ w ≠ w' ∧ z ≠ w * w' := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_natCard_galoisField hq
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hMz : M ∈ centralizingMembers Ω {z} :=
    ⟨hM, le_centralizer_of_commutes (Commutes.symm hKM) hz.mem⟩
  obtain ⟨P, hP, hMP⟩ := typeC_exists_plane_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hMz hMK
  obtain ⟨u, v, huv, rfl⟩ := hP
  obtain ⟨b, hb, hbu, hbv⟩ := exists_symplectic_basis_three u v huv
  subst hbu hbv
  set g : StatedSp 3 (GaloisField p f) := ofSymplecticBasis b hb with hg
  have hgb : ∀ x, CFSG.LieType.Universal.Symplectic.SpExtras.mat 3 (GaloisField p f) g *ᵥ
      Pi.single x 1 = b x := mat_ofSymplecticBasis_mulVec_single b hb
  have hplane : ∀ i : Fin 3, planeGroup (Submodule.span (GaloisField p f)
      {b (Sum.inl i), b (Sum.inr i)}) =
      (planeGroup (stdPlane (GaloisField p f) 3 i)).map (MulAut.conj g).toMonoidHom := by
    intro i
    have := planeGroup_span_conj g (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1)
    rwa [hgb, hgb] at this
  have hP' : IsHyperbolicPlane (Submodule.span (GaloisField p f)
      {b (Sum.inl 1), b (Sum.inr 1)}) :=
    ⟨b (Sum.inl 1), b (Sum.inr 1), by rw [hb, gram_apply]; simp [par, sgn], rfl⟩
  obtain ⟨M', hM'z, hM'K, hM'P⟩ :=
    typeC_exists_member_of_plane (by norm_num) hq hΩ hK hz hP1 d hP'
  have hM'Ω : M' ∈ Ω := hM'z.1
  obtain ⟨w', hw'⟩ := hΩ.classical M' hM'Ω
  have hMY : M ≤ locLayer Ω z := le_centralizingLayer hMz
  have hM'Y : M' ≤ locLayer Ω z := le_centralizingLayer hM'z
  set φ : StatedSp 3 (GaloisField p f) →* locQuot Ω z :=
    d.ψ.comp (MulAut.conj g).toMonoidHom with hφ
  have hφker : φ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField p f)) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ d.ψ.ker := hx
    exact mem_center_of_conj_mem_center (d.ker_le hx')
  have hMimg : locImg Ω z M = (planeGroup (stdPlane (GaloisField p f) 3 0)).map φ := by
    rw [hMP, hplane 0, Subgroup.map_map]
  have hM'img : locImg Ω z M' = (planeGroup (stdPlane (GaloisField p f) 3 1)).map φ := by
    rw [hM'P, hplane 1, Subgroup.map_map]
  have hxw : φ (longInv (GaloisField p f) 3 0) = locElt Ω z w (hMY hw.mem) :=
    hom_longInv_eq_of_mem h2 φ hφker (l := 1) (by decide)
      (hMimg ▸ locElt_mem_locImg hMY hw.mem) (orderOf_locElt (hMY hw.mem) hw.orderOf_eq_two)
  have hxw' : φ (longInv (GaloisField p f) 3 1) = locElt Ω z w' (hM'Y hw'.mem) :=
    hom_longInv_eq_of_mem h2 φ hφker (l := 0) (by decide)
      (hM'img ▸ locElt_mem_locImg hM'Y hw'.mem) (orderOf_locElt (hM'Y hw'.mem) hw'.orderOf_eq_two)
  have hsq0 : longInv (GaloisField p f) 3 0 * longInv (GaloisField p f) 3 0 = 1 :=
    (isLongRootSp2_standard (K := GaloisField p f) (n := 3) 0).mul_self h2
  refine ⟨M', w', hM'Ω, hw', hM'K,
    typeC_commutes_K_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hM'z hM'K, ?_, ?_, ?_⟩
  · refine commutes_of_commutes_locImg hΩ hP1 hMz hM'z ?_
    rw [hMimg, hM'img]
    refine commutes_map_of_commutes φ ?_
    intro x hx y hy
    rw [planeGroup_stdPlane] at hx hy
    exact (commute_longRootSp2 (by decide) hx hy).eq
  · intro hww
    subst hww
    have hmem : longInv (GaloisField p f) 3 0 * longInv (GaloisField p f) 3 1 ∈ φ.ker := by
      have e : φ (longInv (GaloisField p f) 3 1) = φ (longInv (GaloisField p f) 3 0) :=
        hxw'.trans hxw.symm
      rw [MonoidHom.mem_ker, map_mul, e, ← map_mul, hsq0, map_one]
    exact longInv_mul_not_mem_center h2 (hφker hmem)
  · intro hzww
    have hzY : z ∈ locLayer Ω z := le_centralizingLayer hKz hz.mem
    have hzb : locElt Ω z z hzY =
        φ (longInv (GaloisField p f) 3 0 * longInv (GaloisField p f) 3 1) := by
      rw [map_mul, hxw, hxw', locElt_mul]
      unfold locElt
      congr 2
    have hzbK : locElt Ω z z hzY ∈ d.Q₀ :=
      typeC_locImg_self_le_Q₀ (by norm_num) hq hK hz d
        (locElt_mem_locImg (le_centralizingLayer hKz) hz.mem)
    have hcomm : ∀ s : StatedSp 3 (GaloisField p f),
        ⁅longInv (GaloisField p f) 3 0 * longInv (GaloisField p f) 3 1, s⁆ ∈
          Subgroup.center (StatedSp 3 (GaloisField p f)) := by
      intro s
      apply hφker
      rw [MonoidHom.mem_ker, map_commutatorElement, ← hzb, commutatorElement_eq_one_iff_mul_comm]
      exact d.commutes _ hzbK _ ⟨g * s * g⁻¹, rfl⟩
    exact longInv_mul_not_mem_center h2
      (mem_center_of_forall_commutator_mem_center (isPerfect_statedSp_of_four_le h4) hcomm)

end Triple

end CFSG.ClassicalInvolution.RouteD.NonClassical

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime]

theorem sp3TwinP1_of_triangleInputs (hlay : TriangleLayers p f)
    (htri : TriangleConnectedAll p f) : Sp3TwinP1 p f := by
  intro G _ _ _ hnab K z S hS M hM w hw hMK hKM
  classical
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := S.five
      simp at this
    · exact h
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (mem_conjClass_self K) S.cls
    (localShapeC_of_T hS)
  obtain ⟨M', w', hM'Ω, hw', hM'K, hKM', hMM', hww', hzww'⟩ :=
    exists_twin_triple S.odd S.five S.inClass S.exact (mem_conjClass_self K) S.cls S.p1 d hM hw
      hMK hKM
  have hz2 : z * z = 1 := DeltaClosure.sq_eq_one S.cls
  have hw2 : w * w = 1 := DeltaClosure.sq_eq_one hw
  have hw'2 : w' * w' = 1 := DeltaClosure.sq_eq_one hw'
  have hzw : z * w = w * z := hKM z S.cls.mem w hw.mem
  have hzw' : z * w' = w' * z := hKM' z S.cls.mem w' hw'.mem
  have hww'c : w * w' = w' * w := hMM' w hw.mem w' hw'.mem
  have hne1 : ∀ {N : Subgroup G} {y : G}, IsClassicalMember p f N y → y ≠ 1 := fun hy h => by
    have := hy.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hzw_ne : z ≠ w := fun h => not_mem_of_commutes_ne S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 d hM hMK hKM (h ▸ hw.mem)
  have hzw'_ne : z ≠ w' := fun h => not_mem_of_commutes_ne S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 d hM'Ω hM'K hKM' (h ▸ hw'.mem)
  have hcard : Nat.card (Subgroup.closure ({z, w, w'} : Set G)) = 8 :=
    card_closure_three_involutions hz2 hw2 hw'2 hzw hzw' hww'c (hne1 S.cls) (hne1 hw) (hne1 hw')
      hzw_ne hzw'_ne hww' hzww'
  have hmem : ∀ i : Fin 3, ![K, M, M'] i ∈ conjClass K ∧
      IsClassicalMember p f (![K, M, M'] i) (![z, w, w'] i) := by
    intro i
    fin_cases i
    · exact ⟨mem_conjClass_self K, S.cls⟩
    · exact ⟨hM, hw⟩
    · exact ⟨hM'Ω, hw'⟩
  have hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ ![K, M, M'] i, ∀ y ∈ ![K, M, M'] j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hKM x hx y hy
    · exact hKM' x hx y hy
    · exact (hKM y hy x hx).symm
    · exact absurd rfl hij
    · exact hMM' x hx y hy
    · exact (hKM' y hy x hx).symm
    · exact (hMM' y hy x hx).symm
    · exact absurd rfl hij
  have hrange : Subgroup.closure ({z, w, w'} : Set G) =
      Subgroup.closure (Set.range ![z, w, w']) := by
    congr 1
    ext x
    simp
    tauto
  have hel : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({z, w, w'} : Set G)) := by
    refine isElemAbelian_closure_of_commuting_involutions ?_ ?_
    · rintro s (rfl | rfl | rfl)
      · exact hz2
      · exact hw2
      · exact hw'2
    · rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl)
      · rfl
      · exact hzw
      · exact hzw'
      · exact hzw.symm
      · rfl
      · exact hww'c
      · exact hzw'.symm
      · exact hww'c.symm
      · rfl
  have hA : IndepTripleOn p f (conjClass K) (Subgroup.closure ({z, w, w'} : Set G)) :=
    ⟨![K, M, M'], ![z, w, w'], hmem, hcomm, hrange, hel, hcard⟩
  have hlay' : ∀ A' : Subgroup G, IndepTripleOn p f (conjClass K) A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt (conjClass K) A' a := fun A' hA' =>
    hlay G hnab S.odd S.five K z S.cls S.below S.conn A' hA'
  have hbal : ∀ A ∈ triangleFrames p f (conjClass K), RankThreeBalance A := fun A hA =>
    rankThreeBalance_of_indepTripleOn_of_layers hnab S.odd hf S.five S.inClass S.ih hA (hlay' A hA)
  have hα := alphaCore_eq_bot_of_connected_frames (𝒯 := triangleFrames p f (conjClass K))
    (componentClassificationOddCore_eq_bot_of_simple hnab)
    (fun A hA g => indepTripleOn_map S.inClass.conjInvariant hA g) hbal
    (htri G hnab S.odd S.five K z S.cls S.below S.conn)
  obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal _ hA)
  have hx : z * w ∈ Subgroup.closure
      ({(![z, w, w'] : Fin 3 → G) 0, (![z, w, w'] : Fin 3 → G) 1} : Set G) := by
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
    · simp
    · simp
  have hx1 : z * w ≠ 1 := by
    intro h1
    exact hzw_ne (by
      calc z = z * (w * w) := by rw [hw2, mul_one]
        _ = (z * w) * w := by rw [mul_assoc]
        _ = w := by rw [h1, one_mul])
  exact localOddCentral_of_indepTriple_pair hnab S.odd S.five S.inClass S.ih S.exact hlay'
    hmem hcomm hrange hel hcard hF₀ (hα _ hA F₀ hF₀) (i := 0) (j := 1) (by decide) hx hx1

end CFSG.ClassicalInvolution.Generic.CoreAssembly
