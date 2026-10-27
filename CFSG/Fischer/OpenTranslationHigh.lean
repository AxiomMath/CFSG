module

public import CFSG.Fischer.OpenTranslation

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Open

variable {X : Type} [Group X]

theorem F23_of_typeF23_open {E : Set X} (hP : Pair X E) (h : fischerEUTypeF23 E) : F23 X E := by
  obtain ⟨e, he, hpair, h22⟩ := h
  rw [fischerEULocalClass_eq'] at hpair h22
  have := Pair.finite hP
  have hP' : Pair (LocalQuotient E e) (LocalImages E e) := (pair_iff _).2 ⟨inferInstance, hpair⟩
  exact ⟨hP, e, he, F22_of_typeF22_open hP' h22⟩

theorem F24.typeF24_open {E : Set X} (h : F24 X E) : fischerEUTypeF24 E := by
  obtain ⟨-, e, he, h23⟩ := h
  refine ⟨e, he, ?_, ?_⟩
  · rw [fischerEULocalClass_eq']
    exact ((pair_iff _).1 h23.1).2
  · rw [fischerEULocalClass_eq']
    exact F23.typeF23_open h23

theorem F24_of_typeF24_open {E : Set X} (hP : Pair X E) (h : fischerEUTypeF24 E) : F24 X E := by
  obtain ⟨e, he, hpair, h23⟩ := h
  rw [fischerEULocalClass_eq'] at hpair h23
  have := Pair.finite hP
  have hP' : Pair (LocalQuotient E e) (LocalImages E e) := (pair_iff _).2 ⟨inferInstance, hpair⟩
  exact ⟨hP, e, he, F23_of_typeF23_open hP' h23⟩

end CFSG.Fischer
