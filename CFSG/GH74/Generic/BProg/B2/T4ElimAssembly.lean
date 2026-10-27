module

public import CFSG.GH74.Generic.BProg.B2.T4ElimOut
public import CFSG.GH74.Generic.BProg.B2.T4ElimSD
public import CFSG.GH74.Generic.BProg.B2.T4ElimE8
public import CFSG.GH74.Generic.BProg.B2.PuL4Gen4
public import CFSG.GH74.Generic.BProg.B2.Prop31
public import CFSG.GH74.Generic.BProg.Stage1Split

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

namespace T4ElimAssembly

theorem qShape1_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape1 A) :
    QShape1 B := IsSL4Model.of_mulEquiv h e

theorem qShape3_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape3 A) :
    QShape3 B := by
  obtain ⟨p, f, hp, hp2, hq, h⟩ := h
  refine ⟨p, f, hp, hp2, hq, ?_⟩
  rcases h with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)

theorem qShape4_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape4 A) :
    QShape4 B := by
  obtain ⟨f, h⟩ := h
  exact ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h⟩

theorem qShape5_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape5 A) :
    QShape5 B := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩


section Abstract

variable {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}


theorem no_shape45 (hPU : PumpupTableU) (hO : OutG2Comm) (hs : ShapeInCent H t L)
    (hGH : GHList ↥H) (ht : t ∈ commutator N)
    (h45 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      (QShape4 (↥L ⧸ Z) ∨ QShape5 (↥L ⧸ Z))) : False := by
  rcases hPU N H t L hs hGH with h5 | h4 | h3 | h2
  · exact T4ElimE8.false_of_shape45_puL5 hs h5 h45
  · exact T4ElimE8.false_of_shape45_puL4 hs h4 h45
  · exact false_of_shape_puL3sq hs h3 ht
  · exact false_of_shape_puG2 hO hs h2 ht

theorem false_of_shape5 (hPU : PumpupTableU) (hO : OutG2Comm) (hs : ShapeInCent H t L)
    (hGH : GHList ↥H) (ht : t ∈ commutator N)
    (h5 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      QShape5 (↥L ⧸ Z)) : False := by
  obtain ⟨Z, hZc, hZo, hZn, h⟩ := h5
  exact no_shape45 hPU hO hs hGH ht ⟨Z, hZc, hZo, hZn, Or.inr h⟩

theorem false_of_shape4 (hPU : PumpupTableU) (hO : OutG2Comm) (hs : ShapeInCent H t L)
    (hGH : GHList ↥H) (ht : t ∈ commutator N)
    (h4 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      QShape4 (↥L ⧸ Z)) : False := by
  obtain ⟨Z, hZc, hZo, hZn, h⟩ := h4
  exact no_shape45 hPU hO hs hGH ht ⟨Z, hZc, hZo, hZn, Or.inl h⟩

theorem puL5_of_shape13 (hPU : PumpupTableU) (hO : OutG2Comm) (hG4 : Gen4 N)
    (hs : ShapeInCent H t L) (hGH : GHList ↥H) (ht : t ∈ commutator N)
    (h13 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      (QShape1 (↥L ⧸ Z) ∨ QShape3 (↥L ⧸ Z))) : PuL5 ↥H ∧ t ∈ H := by
  rcases hPU N H t L hs hGH with h5 | h4 | h3 | h2
  · exact ⟨h5, mem_of_commutator_puL5 hs.normal hs.faithful h5 ht hs.inv⟩
  · rcases puL4_cases h4 with hSD | hW
    · have htH : t ∈ H := commutator_le_of_puL4SD hs.normal hs.faithful hSD ht
      obtain ⟨Z, hZc, hZo, hZn, h1 | h3'⟩ := h13
      · exact (T4ElimSD.false_of_inner_shape1_SD hs hSD htH ⟨Z, hZc, hZo, hZn, h1⟩).elim
      · exact (PuL4InnerSD.false_of_inner_shape3_SD hs hSD htH ⟨Z, hZc, hZo, hZn, h3'⟩).elim
    · exact (PuL4Gen4.false_of_shape_puL4W hs hW ht hG4).elim
  · exact (false_of_shape_puL3sq hs h3 ht).elim
  · exact (false_of_shape_puG2 hO hs h2 ht).elim

end Abstract

section Group

variable {G : Type} [Group G] [Finite G]

theorem exists_shape_iso {K M : Subgroup G} (hKM : K ≤ M) (hq : IsQuasisimple ↥(barIn M K)) :
    ∃ Z : Subgroup ↥(barIn M K), Z ≤ center ↥(barIn M K) ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* (↥(barIn M K) ⧸ Z)) := by
  let φ : ↥K →* ↥(barIn M K) :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM)).codRestrict (barIn M K)
      (fun k => ⟨Subgroup.inclusion hKM k, k.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥K :=
    (MonoidHom.ker_codRestrict _ _ _).le.trans (Prop31.ker_le_pPrimeCore hKM)
  obtain ⟨Z, hZ, hodd, ⟨e⟩⟩ := Prop31.exists_odd_quotient_equiv φ hφs hker
  exact ⟨Z, Prop31.normal_le_center_of_odd hq hZ hodd, hodd, hZ, ⟨e⟩⟩

omit [Finite G] in
theorem mk_mem_commutator {M : Subgroup G} {x : G} (hx : x ∈ derivedIn M) (hxM : x ∈ M) :
    (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) ∈ commutator (Mbar M) := by
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx
  have hmx' : m = ⟨x, hxM⟩ := Subtype.ext hmx
  have h : (commutator ↥M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤ commutator (Mbar M) := by
    change (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map _ ≤
      ⁅(⊤ : Subgroup (Mbar M)), (⊤ : Subgroup (Mbar M))⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have := h ⟨m, hm, rfl⟩
  rw [hmx'] at this
  exact this

theorem shape1_of_lie_of_B3a (hB3 : ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H :
    Subgroup G), Stage2Setup G x K A M P Q → Stage2Concl1 x K M Q H → Stage3A x A M H → PuL5 ↥(barIn
    M H) → QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → False) (hPU : PumpupTableU) (hO : OutG2Comm)
    (hB : B_B2_g4) {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (h3 : Stage3A x A M H) (_hL : OfLieType ↥(barIn M H)) :
    QShape1 (↥K ⧸ pPrimeCore 2 ↥K) ∧ PuL5 ↥(barIn M H) ∧
      ∃ hxM : x ∈ M, (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) ∈ barIn M H := by
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxM : x ∈ M := h3.Cx_le hxC
  have hcomp := Prop31.isCompIn_barIn_centralizer hB hs hxM h3.Cx_le
  have hshape := shapeInCent_of_isCompIn hs (Stage2Concl1.toCore h1) h3 hxM hcomp
  have hGH := ghList_barIn hs h3
  have ht := mk_mem_commutator h3.x_mem hxM
  have hG4 : Gen4 (Mbar M) := Gen4.quotient (pPrimeCore 2 ↥M) (Gen4.subgroup M hs.hyp.gen4)
  obtain ⟨Z, hZc, hZo, hZn, ⟨e⟩⟩ :=
    exists_shape_iso h1.K_le (Prop31.isQuasisimple_of_isCompIn hcomp)
  rcases qShapeNS_of_isSource2 hs.src with k1 | k3 | k4 | k5
  · obtain ⟨hL5, hxH⟩ := puL5_of_shape13 hPU hO hG4 hshape hGH ht
      ⟨Z, hZc, hZo, hZn, Or.inl (qShape1_of_equiv e k1)⟩
    exact ⟨k1, hL5, hxM, hxH⟩
  · exfalso
    obtain ⟨hL5, -⟩ := puL5_of_shape13 hPU hO hG4 hshape hGH ht
      ⟨Z, hZc, hZo, hZn, Or.inr (qShape3_of_equiv e k3)⟩
    exact hB3 G x K A M P Q H hs h1 h3 hL5 k3
  · exact (false_of_shape4 hPU hO hshape hGH ht
      ⟨Z, hZc, hZo, hZn, qShape4_of_equiv e k4⟩).elim
  · exact (false_of_shape5 hPU hO hshape hGH ht
      ⟨Z, hZc, hZo, hZn, qShape5_of_equiv e k5⟩).elim

end Group

end T4ElimAssembly

end CFSG.GH74.Generic.BProg.B2.T4
