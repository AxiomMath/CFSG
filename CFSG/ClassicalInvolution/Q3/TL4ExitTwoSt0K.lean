module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0A
public import CFSG.ClassicalInvolution.Q3.TL4E3Norm
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

omit [Finite G] in
theorem nonempty_equiv_of_surjective (hL₀ : CFSG.IsComponent L₀) (hn : L₀.Normal)
    {W : Subgroup G} (hLW : L₀ ≤ W) {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) (f : ↥W →* Q) (hf : Function.Surjective f)
    (hker : ∀ w ∈ f.ker, (w : G) ∈ Subgroup.center G) :
    Nonempty (↥L₀ ⧸ Subgroup.center ↥L₀ ≃* Q) := by
  set φ : ↥L₀ →* Q := f.comp (Subgroup.inclusion hLW) with hφ
  have hrange : φ.range = (L₀.subgroupOf W).map f := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hnorm : φ.range.Normal := by
    rw [hrange]
    have : (L₀.subgroupOf W).Normal := Subgroup.normal_subgroupOf
    exact Subgroup.Normal.map this f hf
  have hφs : Function.Surjective φ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.range with h | h
    · exfalso
      have hall : ∀ m : ↥L₀, (m : G) ∈ Subgroup.center G := by
        intro m
        have h1 : φ m ∈ φ.range := ⟨m, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact hker (Subgroup.inclusion hLW m) (MonoidHom.mem_ker.mpr h1)
      obtain ⟨a, b, hab⟩ := hL₀.1.2.2
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hall b) a)
    · exact MonoidHom.range_eq_top.mp h
  have hker' : φ.ker = Subgroup.center ↥L₀ := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro hm
      have hmG : (m : G) ∈ Subgroup.center G :=
        hker (Subgroup.inclusion hLW m) (MonoidHom.mem_ker.mpr hm)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hmG g)
    · intro hm
      have hc : φ m ∈ Subgroup.center Q := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨a, rfl⟩ := hφs q
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hm a]
      rw [center_eq_bot_of_isSimpleGroup hQ, Subgroup.mem_bot] at hc
      exact hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem simple_nonabelian_of_e4 {Q : Type} [Group Q]
    (hQ : LieModel Q .PSp 3 2 1 ∨ LieModel Q .POmegaPlus 4 2 1) :
    IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
  have hs : IsSimpleGroup Q := by
    rcases hQ with h | h <;> exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
  have hcard : ¬ (Nat.card Q).Prime := by
    rcases hQ with h | h
    · rw [card_of_lieModel_psp_three_two_one h]
      norm_num
    · rw [card_of_lieModel_pomegaPlus_four_two_one h]
      norm_num
  exact ⟨hs, exists_ne_comm_of_not_prime hcard⟩

omit [Finite G] in
theorem socleType_of_e4_equiv {Q : Type} [Group Q] (e : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃* Q)
    (hQ : LieModel Q .PSp 3 2 1 ∨ LieModel Q .POmegaPlus 4 2 1) :
    SocleType (↥L₀ ⧸ Subgroup.center ↥L₀) := by
  rcases hQ with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))))))

theorem socleType_of_twinE4 (hc : F2CoreConfig J L L₀) {W : Subgroup G} (hWs : IsSubnormal W ⊤)
    (hLW : L₀ ≤ W) (h : PhilipHall.Frame.TwinE4 ↥W) :
    SocleType (↥L₀ ⧸ Subgroup.center ↥L₀) := by
  obtain ⟨-, -, -, -, -, hL₀, hn, -, -, -, -, -⟩ := id hc
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  obtain ⟨hs, hnab⟩ := simple_nonabelian_of_e4 hQ
  have hker : ∀ w ∈ f.ker, (w : G) ∈ Subgroup.center G := fun w hw =>
    mem_center_of_tightInO2 hc hWs ⟨f.ker, MonoidHom.normal_ker f, hf2, hw⟩
  obtain ⟨e⟩ := nonempty_equiv_of_surjective hL₀ hn hLW hnab f hfs hker
  exact socleType_of_e4_equiv e hQ

theorem socleType_of_center_E4 (hc : F2CoreConfig J L L₀) {W : Subgroup G} (hLW : L₀ ≤ W)
    (h : LieModel (↥W ⧸ Subgroup.center ↥W) .PSp 3 2 1 ∨
      LieModel (↥W ⧸ Subgroup.center ↥W) .POmegaPlus 4 2 1) :
    SocleType (↥L₀ ⧸ Subgroup.center ↥L₀) := by
  obtain ⟨-, -, -, -, -, hL₀, hn, -, -, -, hC, -⟩ := id hc
  obtain ⟨hs, hnab⟩ := simple_nonabelian_of_e4 h
  have hker : ∀ w ∈ (QuotientGroup.mk' (Subgroup.center ↥W)).ker,
      (w : G) ∈ Subgroup.center G := fun w hw =>
    mem_center_of_mem_center hC hLW (by rwa [QuotientGroup.ker_mk'] at hw)
  obtain ⟨e⟩ := nonempty_equiv_of_surjective hL₀ hn hLW hnab _
    (QuotientGroup.mk'_surjective _) hker
  exact socleType_of_e4_equiv e h

theorem socleType_of_center_M12 (hc : F2CoreConfig J L L₀)
    {W : Subgroup G} (hLW : L₀ ≤ W)
    (h : Nonempty (↥W ⧸ Subgroup.center ↥W ≃* NativeSporadic.Carrier .M12)) :
    SocleType (↥L₀ ⧸ Subgroup.center ↥L₀) := by
  obtain ⟨-, -, -, -, -, hL₀, hn, -, -, -, hC, -⟩ := id hc
  obtain ⟨e₀⟩ := h
  have hs : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hcard : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have hnab := exists_ne_comm_of_not_prime (Q := NativeSporadic.Carrier .M12)
    (by rw [hcard]; norm_num)
  have hker : ∀ w ∈ (e₀.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥W))).ker,
      (w : G) ∈ Subgroup.center G := by
    intro w hw
    have hw' : QuotientGroup.mk' (Subgroup.center ↥W) w = 1 := by
      have h1 : e₀ (QuotientGroup.mk' (Subgroup.center ↥W) w) = 1 := hw
      simpa using h1
    have hwZ : w ∈ Subgroup.center ↥W := (QuotientGroup.eq_one_iff _).mp hw'
    exact mem_center_of_mem_center hC hLW hwZ
  obtain ⟨e⟩ := nonempty_equiv_of_surjective hL₀ hn hLW hnab _
    (e₀.surjective.comp (QuotientGroup.mk'_surjective _)) hker
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
