module

public import Certificates.Certificate27800

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8J

noncomputable def Jsub : Subgroup (Equiv.Perm (Fin 820)) :=
  Classical.choose Certificates.certificate27800

theorem Jsub_le : Jsub ≤ U43Ext :=
  (Classical.choose_spec Certificates.certificate27800).1

theorem card_Jsub :
    Nat.card (Jsub : Subgroup (Equiv.Perm (Fin 820))) = 256 :=
  (Classical.choose_spec Certificates.certificate27800).2.1

theorem table_conj {ζ α t g₁ g₂ h₁ h₂ : Equiv.Perm (Fin 820)}
    (hζ : ζ ∈ Jsub) (hα : α ∈ Jsub) (ht : t ∈ Jsub) (hg₁ : g₁ ∈ Jsub) (hg₂ : g₂ ∈ Jsub)
    (hh₁ : h₁ ∈ Jsub) (hh₂ : h₂ ∈ Jsub) (hT : OuterTable ζ α t g₁ g₂ h₁ h₂) :
    ∃ k ∈ U43Ext, k * ζ * k⁻¹ = α :=
  (Classical.choose_spec Certificates.certificate27800).2.2 ζ hζ α hα t ht g₁ hg₁ g₂ hg₂
    h₁ hh₁ h₂ hh₂ hT

end CFSG.EvenSporadicStandard.Fin76b.TS8J
