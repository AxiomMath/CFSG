module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GLTwoHabDischarge

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.B6
  CFSG.Quasithin.E2 CFSG.AGLEmbeddingD2.GN

theorem comm_of_isPGroup_le_iSup {A : Type*} [Group A] {ι : Type*} [Fintype ι]
    (H : ι → Subgroup A)
    (hcomm : Pairwise fun i j : ι => ∀ x y : A, x ∈ H i → y ∈ H j → Commute x y)
    (hz : ∀ i, ∀ z ∈ H i, (∀ x ∈ H i, z * x = x * z) → z = 1)
    (h2 : ∀ i, ∀ Q : Subgroup A, Q ≤ H i → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    {Q : Subgroup A} (hQ : IsPGroup 2 Q) (hle : Q ≤ ⨆ i, H i) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  classical
  have hind : iSupIndep H := by
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxi hxj
    have hcen : (⨆ j, ⨆ (_ : j ≠ i), H j : Subgroup A) ≤ Subgroup.centralizer (H i : Set A) :=
      iSup₂_le fun j hj y hy z hz => (hcomm hj y z hy hz).eq.symm
    refine hz i x hxi fun y hy => ?_
    exact (hcen hxj y hy).symm
  set φ := Subgroup.noncommPiCoprod hcomm with hφ
  have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  set Q₀ : Subgroup (∀ i, H i) := Q.comap φ with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := hQ.comap_of_injective φ hinj
  have hcoord : ∀ i, ∀ u ∈ Q₀, ∀ v ∈ Q₀, u i * v i = v i * u i := by
    intro i u hu v hv
    set T : Subgroup (H i) := Q₀.map (Pi.evalMonoidHom (fun j => H j) i) with hT
    have hT2 : IsPGroup 2 T := hQ₀2.map _
    have hT' : IsPGroup 2 (T.map (H i).subtype) := hT2.map _
    have hle' : T.map (H i).subtype ≤ H i := by
      rintro _ ⟨t, -, rfl⟩
      exact t.2
    have hui : (u i : A) ∈ T.map (H i).subtype := ⟨u i, ⟨u, hu, rfl⟩, rfl⟩
    have hvi : (v i : A) ∈ T.map (H i).subtype := ⟨v i, ⟨v, hv, rfl⟩, rfl⟩
    exact Subtype.ext (h2 i _ hle' hT' _ hui _ hvi)
  intro x hx y hy
  have hxr : x ∈ φ.range := by rw [hrange]; exact hle hx
  have hyr : y ∈ φ.range := by rw [hrange]; exact hle hy
  obtain ⟨u, rfl⟩ := hxr
  obtain ⟨v, rfl⟩ := hyr
  have hu : u ∈ Q₀ := hx
  have hv : v ∈ Q₀ := hy
  rw [← map_mul, ← map_mul]
  congr 1
  funext i
  exact hcoord i u hu v hv


section Natural

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {C : Subgroup W} {n : ℕ}

theorem isL2Natural_center_trivial (h : IsL2Natural L C n) :
    ∀ z ∈ L, (∀ x ∈ L, z * x = x * z) → z = 1 := by
  intro z hz hzc
  obtain ⟨hn, F, _, _, hF, e, -⟩ := h
  have h2d : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    exact dvd_pow_self 2 (by omega)
  have hchar : CharP F 2 :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GLTwoHabDischarge.charP_two_of_two_dvd_card F h2d
  have hcen : e ⟨z, hz⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨x, rfl⟩ := e.surjective B
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hzc x x.2).symm)
  obtain ⟨r, hr, hre⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hsq)
  subst hr1
  have : e ⟨z, hz⟩ = 1 := Subtype.ext (by simpa using hre.symm)
  exact congrArg Subtype.val (e.injective (this.trans (map_one e).symm))

theorem isL2Natural_comm_of_isPGroup (h : IsL2Natural L C n) {Q : Subgroup (MulAut W)}
    (hQL : Q ≤ L) (hQ : IsPGroup 2 Q) : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  obtain ⟨hn, F, _, _, hF, e, -⟩ := h
  have h2d : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    exact dvd_pow_self 2 (by omega)
  let g : ↥L →* GL (Fin 2) F :=
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := F)).comp e.toMonoidHom
  have hg : Function.Injective g :=
    Matrix.SpecialLinearGroup.toGL_injective.comp e.injective
  have hQ' : IsPGroup 2 (Q.subgroupOf L) := hQ.comap_subtype
  have hcomm := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GLTwoHabDischarge.isMulCommutative_of_two_dvd_card_GL2
    h2d ((Q.subgroupOf L).map g) (hQ'.map g)
  intro x hx y hy
  have hxL : x ∈ L := hQL hx
  have hyL : y ∈ L := hQL hy
  have key := hcomm.is_comm.comm
    ⟨g ⟨x, hxL⟩, ⟨⟨x, hxL⟩, hx, rfl⟩⟩ ⟨g ⟨y, hyL⟩, ⟨⟨y, hyL⟩, hy, rfl⟩⟩
  have key2 : g ⟨x, hxL⟩ * g ⟨y, hyL⟩ = g ⟨y, hyL⟩ * g ⟨x, hxL⟩ := congrArg Subtype.val key
  rw [← map_mul, ← map_mul] at key2
  exact congrArg Subtype.val (hg key2)

end Natural


section Family

variable {G : Type} [Group G] {H T V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem comm_of_isPGroup_le_iSup_of_fam (hFam : E23FamGen H T V hV I)
    (hn : ∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    {Q : Subgroup (MulAut (IntMod V hV))} (hQ : IsPGroup 2 Q) (hle : Q ≤ ⨆ L ∈ I, L) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  classical
  have hcomm := hFam.2.2.1
  refine comm_of_isPGroup_le_iSup (ι := ↥I) (fun L => (L : Subgroup (MulAut (IntMod V hV))))
    ?_ ?_ ?_ hQ ?_
  · intro i j hij x y hx hy
    have hne : (i : Subgroup (MulAut (IntMod V hV))) ≠ j := fun h => hij (Subtype.ext h)
    exact hcomm _ i.2 _ j.2 hne x hx y hy
  · intro i z hz hzc
    obtain ⟨n, hn'⟩ := hn i i.2
    exact isL2Natural_center_trivial hn' z hz hzc
  · intro i Q' hQ'L hQ'
    obtain ⟨n, hn'⟩ := hn i i.2
    exact isL2Natural_comm_of_isPGroup hn' hQ'L hQ'
  · rw [iSup_subtype'] at hle
    exact hle

end Family

end CFSG.AGLEmbeddingD2.Tits.GN516
