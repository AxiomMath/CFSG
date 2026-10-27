module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Recognition
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerBasic
public import CFSG.ClassicalInvolution.RouteD.TypeF4Nodes

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock longInv)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

abbrev F4Layer (p f : ℕ) [Fact p.Prime] : Type :=
  Option {R : Subgroup (StatedSp 3 (GaloisField p f)) //
    R ∈ planeGroupSet (GaloisField p f) 3 ∧
      R ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _)}

@[expose] def F4Layer.rel : F4Layer p f → F4Layer p f → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some R, some R' => Commutes R.1 R'.1

section Inv

variable [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem psi_longInv (hp2 : p ≠ 2) (d : ShapeCDict p f 3 Ω z) {j₀ : Subgroup G}
    (hj₀Y : j₀ ≤ locLayer Ω z)
    (hj₀img : locImg Ω z j₀ =
      (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ) {w₀ : G}
    (hw₀ : w₀ ∈ j₀) (hw₀2 : orderOf w₀ = 2) :
    d.ψ (longInv (GaloisField p f) 3 (Fin.last 2)) = locElt Ω z w₀ (hj₀Y hw₀) := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hmem : locElt Ω z w₀ (hj₀Y hw₀) ∈ locImg Ω z j₀ := locElt_mem_locImg hj₀Y hw₀
  rw [hj₀img] at hmem
  obtain ⟨k, hk, hkw⟩ := hmem
  rw [Models.SymplecticPairs.planeGroup_stdPlane] at hk
  obtain ⟨s, rfl⟩ := hk
  have hord : orderOf (locElt Ω z w₀ (hj₀Y hw₀)) = 2 := orderOf_locElt (hj₀Y hw₀) hw₀2
  have hsq : d.ψ (longBlock (GaloisField p f) 3 (Fin.last 2) (s * s)) = 1 := by
    rw [map_mul, map_mul]
    show (d.ψ (longBlock (GaloisField p f) 3 (Fin.last 2) s)) *
      (d.ψ (longBlock (GaloisField p f) 3 (Fin.last 2) s)) = 1
    rw [hkw, ← pow_two]
    have := pow_orderOf_eq_one (locElt Ω z w₀ (hj₀Y hw₀))
    rwa [hord] at this
  have hc : longBlock (GaloisField p f) 3 (Fin.last 2) (s * s) ∈
      Subgroup.center (StatedSp 3 (GaloisField p f)) := d.ker_le (MonoidHom.mem_ker.mpr hsq)
  have hs : longBlock (GaloisField p f) 3 (Fin.last 2) (s * s) ∈
      Models.SymplecticPairs.suppGroup (Models.SymplecticPairs.coords (Fin.last 2) :
        Set (Fin 3 ⊕ Fin 3)) := by
    rw [← Models.SymplecticPairs.range_longBlock]
    exact ⟨_, rfl⟩
  have h1 := Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup hc hs
    (t := Sum.inl (0 : Fin 3)) (by
      simp [Models.SymplecticPairs.mem_coords])
  have hss : s * s = 1 := by
    apply Models.SymplecticPairs.longBlock_injective (Fin.last 2)
    rw [h1, map_one]
  rcases sl2_sq_eq_one h2 hss with h | h
  · exfalso
    subst h
    rw [map_one, map_one] at hkw
    rw [← hkw, orderOf_one] at hord
    omega
  · subst h
    exact hkw

end Inv

section Visible

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_visible_equiv_f4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z) {j₀ : Subgroup G}
    (hj₀ : j₀ ∈ centralizingMembers Ω {z})
    (hj₀img : locImg Ω z j₀ =
      (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ) {w₀ : G}
    (hw₀ : IsClassicalMember p f j₀ w₀) (hKj₀ : Commutes K j₀) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {z * w₀, z}} ≃ F4Layer p f,
      (∀ N N', Commutes N.1 N'.1 ↔ F4Layer.rel (φ N) (φ N')) ∧
        ∀ h : K ∈ centralizingMembers Ω {z * w₀, z}, φ ⟨K, h⟩ = none := by
  classical
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_natCard_galoisField hq
  have hker := d.ker_le
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hj₀Y : j₀ ≤ locLayer Ω z := le_centralizingLayer hj₀
  have hw₀Y : w₀ ∈ locLayer Ω z := hj₀Y hw₀.mem
  have hψw : d.ψ (longInv (GaloisField p f) 3 (Fin.last 2)) = locElt Ω z w₀ hw₀Y :=
    psi_longInv hp2 d hj₀Y hj₀img hw₀.mem hw₀.orderOf_eq_two
  have hKvis : K ∈ centralizingMembers Ω {z * w₀, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hKz, le_centralizer_of_commutes hKj₀ hw₀.mem⟩
  have hperf : ∀ R ∈ planeGroupSet (GaloisField p f) 3, R ≤ ⁅R, R⁆ := by
    rintro _ ⟨P, hP, rfl⟩
    exact planeGroup_perfect h4 (by norm_num) hP
  have hperf' : ∀ R ∈ planeGroupSet (GaloisField p f) 3, Group.IsPerfect ↥R := fun R hR =>
    Subgroup.isPerfect_iff.mpr (le_antisymm (commutator_self_le _) (hperf R hR))
  have hmem : ∀ ρ : {R : Subgroup (StatedSp 3 (GaloisField p f)) //
      R ∈ planeGroupSet (GaloisField p f) 3 ∧
        R ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _)},
      ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = ρ.1.map d.ψ := by
    rintro ⟨_, ⟨P, hP, rfl⟩, -⟩
    exact typeC_exists_member_of_plane (by norm_num) hq hΩ hK hz hP1 d hP
  choose Lof hLz hLK hLimg using hmem
  have hcent : ∀ {L : Subgroup G}, L ∈ centralizingMembers Ω {z} →
      ∀ {R : Subgroup (StatedSp 3 (GaloisField p f))}, R ≤ ⁅R, R⁆ →
      locImg Ω z L = R.map d.ψ →
      (L ≤ Subgroup.centralizer ({w₀} : Set G) ↔
        R ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _)) := by
    intro L hL R hR hLR
    have h1 := le_centralizer_iff_locImg hΩ hP1 hL ⟨w₀, hw₀Y⟩
    have h2 := le_centralizer_iff_map d.ψ hker hR (longInv (GaloisField p f) 3 (Fin.last 2))
    rw [h2, hψw, ← hLR]
    exact h1
  have hvis : ∀ ρ, Lof ρ ∈ centralizingMembers Ω {z * w₀, z} := by
    intro ρ
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hLz ρ, (hcent (hLz ρ) (hperf _ ρ.2.1) (hLimg ρ)).mpr ρ.2.2⟩
  let ι : F4Layer p f → {N : Subgroup G // N ∈ centralizingMembers Ω {z * w₀, z}} :=
    fun a => Option.elim a ⟨K, hKvis⟩ fun ρ => ⟨Lof ρ, hvis ρ⟩
  have hinj : Function.Injective ι := by
    intro a b hab
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (hLK ρ')
    · exact absurd (congrArg Subtype.val hab) (hLK ρ)
    · have h : Lof ρ = Lof ρ' := congrArg Subtype.val hab
      have himg : ρ.1.map d.ψ = ρ'.1.map d.ψ := by
        rw [← hLimg ρ, ← hLimg ρ', h]
      exact congrArg some (Subtype.ext (eq_of_map_eq_of_central d.ψ hker (hperf _ ρ.2.1)
        (hperf _ ρ'.2.1) himg))
  have hsurj : Function.Surjective ι := by
    rintro ⟨N, hN⟩
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hN
    obtain ⟨hNz, hNw⟩ := hN
    by_cases hNK : N = K
    · exact ⟨none, Subtype.ext hNK.symm⟩
    · obtain ⟨P, hP, hNP⟩ := typeC_exists_plane_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hNz hNK
      have hρc : planeGroup P ≤
          Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _) :=
        (hcent hNz (hperf _ ⟨P, hP, rfl⟩) hNP).mp hNw
      refine ⟨some ⟨planeGroup P, ⟨P, hP, rfl⟩, hρc⟩, Subtype.ext ?_⟩
      exact locImg_injOn hΩ hP1 (hLz _) hNz ((hLimg ⟨planeGroup P, ⟨P, hP, rfl⟩, hρc⟩).trans
        hNP.symm)
  have key : ∀ a b : F4Layer p f, Commutes (ι a).1 (ι b).1 ↔ F4Layer.rel a b := by
    intro a b
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · exact iff_false_intro (not_commutes_self_of_isClassicalMember hz)
    · exact iff_true_intro (typeC_commutes_K_of_ne (by norm_num) hq hΩ hex hK hz hP1 d
        (hLz ρ') (hLK ρ'))
    · exact iff_true_intro (commutes_symm (typeC_commutes_K_of_ne (by norm_num) hq hΩ hex hK hz
        hP1 d (hLz ρ) (hLK ρ)))
    · show Commutes (Lof ρ) (Lof ρ') ↔ Commutes ρ.1 ρ'.1
      constructor
      · intro h
        have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
        rw [hLimg ρ, hLimg ρ'] at h1
        exact commutes_of_commutes_map d.ψ hker (hperf' _ ρ.2.1) h1
      · intro h
        refine commutes_of_commutes_locImg hΩ hP1 (hLz ρ) (hLz ρ') ?_
        rw [hLimg ρ, hLimg ρ']
        exact commutes_map_of_commutes _ h
  refine ⟨(Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm, fun N N' => ?_, fun h => ?_⟩
  · have h1 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N) = N :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N
    have h2 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N') = N' :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N'
    have := key ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N)
      ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N')
    rwa [h1, h2] at this
  · exact (Equiv.symm_apply_eq _).mpr (Subtype.ext rfl)

end Visible

end CFSG.ClassicalInvolution.RouteD.NonClassical
