module

public import CFSG.Fischer.Uniq.LocalHyperoval

public section

namespace CFSG.Fischer

variable {X Y : Type} {A : Set X} {A' : Set Y}

@[expose] def imgIn (φ : A ≃ A') (U : Set X) : Set Y := {y | ∃ x : A, (x : X) ∈ U ∧ (φ x : Y) = y}

theorem mem_imgIn {φ : A ≃ A'} {U : Set X} {y : Y} :
    y ∈ imgIn φ U ↔ ∃ x : A, (x : X) ∈ U ∧ (φ x : Y) = y :=
  Iff.rfl

theorem imgIn_subset (φ : A ≃ A') (U : Set X) : imgIn φ U ⊆ A' := by
  rintro _ ⟨x, -, rfl⟩
  exact (φ x).2

theorem val_mem_imgIn_iff (φ : A ≃ A') (U : Set X) (x : A) :
    (φ x : Y) ∈ imgIn φ U ↔ (x : X) ∈ U := by
  constructor
  · rintro ⟨x', hx', h⟩
    rwa [← φ.injective (Subtype.ext h)]
  · intro h
    exact ⟨x, h, rfl⟩

section Comm

variable [Group X] [Group Y] (φ : A ≃ A')
  (hcomm : ∀ x y : A, (x : X) * y = y * x ↔ (φ x : Y) * φ y = φ y * φ x)
include hcomm

theorem mem_lineIn_iff_of_equiv (x y z : A) :
    (z : X) ∈ lineIn A x y ↔ (φ z : Y) ∈ lineIn A' (φ x) (φ y) := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨(φ z).2, fun w' hw' hwx hwy => ?_⟩
    obtain ⟨w, hw⟩ := φ.surjective ⟨w', hw'⟩
    have hw'' : (φ w : Y) = w' := congrArg Subtype.val hw
    rw [← hw''] at hwx hwy ⊢
    exact (hcomm w z).1 (h w w.2 ((hcomm w x).2 hwx) ((hcomm w y).2 hwy))
  · rintro ⟨-, h⟩
    refine ⟨z.2, fun w hw hwx hwy => ?_⟩
    exact (hcomm ⟨w, hw⟩ z).2 (h _ (φ ⟨w, hw⟩).2 ((hcomm ⟨w, hw⟩ x).1 hwx)
      ((hcomm ⟨w, hw⟩ y).1 hwy))

theorem imgIn_lineIn (x y : A) : imgIn φ (lineIn A x y) = lineIn A' (φ x) (φ y) := by
  ext z'
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_lineIn_iff_of_equiv φ hcomm x y z).1 hz
  · intro hz'
    obtain ⟨z, hz⟩ := φ.surjective ⟨z', hz'.1⟩
    refine ⟨z, (mem_lineIn_iff_of_equiv φ hcomm x y z).2 ?_, congrArg Subtype.val hz⟩
    rw [hz]
    exact hz'

theorem IsLineIn.imgIn {L : Set X} (hL : IsLineIn A L) : IsLineIn A' (imgIn φ L) := by
  obtain ⟨x, hx, y, hy, hne, hxy, rfl⟩ := hL
  refine ⟨φ ⟨x, hx⟩, (φ _).2, φ ⟨y, hy⟩, (φ _).2, fun h => hne ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (φ.injective (Subtype.ext h))
  · exact (hcomm ⟨x, hx⟩ ⟨y, hy⟩).1 hxy
  · exact imgIn_lineIn φ hcomm ⟨x, hx⟩ ⟨y, hy⟩

theorem exists_isLineIn_imgIn {L' : Set Y} (hL' : IsLineIn A' L') :
    ∃ L, IsLineIn A L ∧ imgIn φ L = L' := by
  obtain ⟨x', hx', y', hy', hne, hxy, rfl⟩ := hL'
  obtain ⟨x, hx⟩ := φ.surjective ⟨x', hx'⟩
  obtain ⟨y, hy⟩ := φ.surjective ⟨y', hy'⟩
  refine ⟨lineIn A x y, ⟨x, x.2, y, y.2, fun h => hne ?_, ?_, rfl⟩, ?_⟩
  · have := congrArg φ (Subtype.ext h : x = y)
    rw [hx, hy] at this
    exact congrArg Subtype.val this
  · have := (hcomm x y).2 (by rw [hx, hy]; exact hxy)
    exact this
  · rw [imgIn_lineIn φ hcomm, hx, hy]

omit [Group X] [Group Y] hcomm in
theorem imgIn_inter {L U : Set X} : imgIn φ (L ∩ U) = imgIn φ L ∩ imgIn φ U := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxL, hxU⟩, rfl⟩
    exact ⟨⟨x, hxL, rfl⟩, ⟨x, hxU, rfl⟩⟩
  · rintro ⟨⟨x, hxL, rfl⟩, hy⟩
    exact ⟨x, ⟨hxL, (val_mem_imgIn_iff φ U x).1 hy⟩, rfl⟩

omit [Group X] [Group Y] hcomm in
theorem ncard_imgIn {U : Set X} (hU : U ⊆ A) : (imgIn φ U).ncard = U.ncard := by
  refine Set.ncard_congr (fun y hy => ((φ.symm ⟨y, imgIn_subset φ U hy⟩ : A) : X))
    (fun y hy => ?_) (fun y y' hy hy' e => ?_) (fun x hx => ?_)
  · obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  · have := φ.symm.injective (Subtype.ext e)
    exact congrArg Subtype.val this
  · refine ⟨φ ⟨x, hU hx⟩, ⟨⟨x, hU hx⟩, hx, rfl⟩, ?_⟩
    simp

theorem IsHyperovalIn.transport
    (htau : ∀ x y : A, ∃ h : (x : X) * y * x ∈ A, (φ ⟨_, h⟩ : Y) = φ x * φ y * φ x)
    {U : Set X} (hU : IsHyperovalIn A U) : IsHyperovalIn A' (imgIn φ U) := by
  refine ⟨imgIn_subset φ U, fun L' hL' => ?_, fun x' hx' => ?_⟩
  · obtain ⟨L, hL, rfl⟩ := exists_isLineIn_imgIn φ hcomm hL'
    have hLA : L ⊆ A := by
      obtain ⟨x, -, y, -, -, -, rfl⟩ := hL
      exact fun z hz => hz.1
    rw [← imgIn_inter φ, ncard_imgIn φ (Set.inter_subset_left.trans hLA)]
    exact hU.inter L hL
  · obtain ⟨x, hx, rfl⟩ := hx'
    have hcl := hU.closed x hx
    ext y'
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨h, e⟩ := htau x y
      show (φ x : Y) * φ y * φ x ∈ imgIn φ U
      rw [← e]
      refine ⟨⟨_, h⟩, ?_, rfl⟩
      rw [← hcl]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : X) ∈ (fun z => (x : X) * z * x) '' U := by rw [hcl]; exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      have hzA : z ∈ A := hU.subset hz
      obtain ⟨h, e⟩ := htau x ⟨z, hzA⟩
      refine ⟨φ ⟨z, hzA⟩, ⟨⟨z, hzA⟩, hz, rfl⟩, ?_⟩
      show (φ x : Y) * φ ⟨z, hzA⟩ * φ x = φ y
      rw [← e]
      congr 2
      exact Subtype.ext hzy

omit hcomm in
theorem comm_symm_of_comm (hc : ∀ x y : A, (x : X) * y = y * x ↔ (φ x : Y) * φ y = φ y * φ x)
    (x y : A') : (x : Y) * y = y * x ↔ (φ.symm x : X) * φ.symm y = φ.symm y * φ.symm x := by
  have := hc (φ.symm x) (φ.symm y)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

omit hcomm in
theorem tau_symm_of_tau
    (htau : ∀ x y : A, ∃ h : (x : X) * y * x ∈ A, (φ ⟨_, h⟩ : Y) = φ x * φ y * φ x)
    (x y : A') :
    ∃ h : (x : Y) * y * x ∈ A', (φ.symm ⟨_, h⟩ : X) = φ.symm x * φ.symm y * φ.symm x := by
  obtain ⟨h0, e⟩ := htau (φ.symm x) (φ.symm y)
  simp only [Equiv.apply_symm_apply] at e
  refine ⟨e ▸ (φ ⟨_, h0⟩).2, ?_⟩
  have : (⟨(x : Y) * y * x, e ▸ (φ ⟨_, h0⟩).2⟩ : A') = φ ⟨_, h0⟩ := Subtype.ext e.symm
  rw [this, Equiv.symm_apply_apply]

end Comm

end CFSG.Fischer
