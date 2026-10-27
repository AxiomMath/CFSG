module

public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem elementary_hom_range {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ}
    (Elementary : Subgroup Ambient) (helementary : IsElemAbelian prime Elementary)
    (homomorphism : Elementary →* Target) : IsElemAbelian prime homomorphism.range := by
  have htopElementary : IsElemAbelian prime (⊤ : Subgroup Elementary) := by
    constructor
    · exact ⟨⟨fun first second => by
        apply Subtype.ext
        exact @mul_comm' Elementary _ helementary.1 first.val second.val⟩⟩
    · intro element _
      apply Subtype.ext
      exact helementary.2 element.val element.property
  rw [MonoidHom.range_eq_map]
  exact elementary_map _ htopElementary homomorphism

end CFSG.LargeEvenClassification.Helpers
