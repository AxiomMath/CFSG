module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Coc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Dec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Certificates.AE117 Mdl117

theorem model117_proved : Model117 := by
  intro n hn5 hn7 β hβ
  obtain ⟨⟨hA₅, hA₆, hA₇⟩, ⟨hC₅, hC₆, hC₇⟩, ⟨hG₅, hG₆, hG₇⟩, ⟨hS₅, hS₆, hS₇⟩⟩ := ae117_check
  interval_cases n
  · have hC := cocProp₅_of hC₅
    have hG := genProp₅_of hG₅
    exact model117_of (g₁ := g₁₅) (g₂ := g₂₅) hn5 (by decide) hA₅ hS₅
      (Equiv.Perm.mem_alternatingGroup.mpr (by decide))
      (Equiv.Perm.mem_alternatingGroup.mpr (by decide)) hC hG hβ
  · have hC := cocProp₆_of hC₆
    have hG := genProp₆_of hG₆
    exact model117_of (g₁ := g₁₆) (g₂ := g₂₆) hn5 (by decide) hA₆ hS₆
      (Equiv.Perm.mem_alternatingGroup.mpr (by decide))
      (Equiv.Perm.mem_alternatingGroup.mpr (by decide)) hC hG hβ
  · have hC := cocProp₇_of hC₇
    have hG := genProp₇_of hG₇
    exact model117_of (g₁ := g₁₇) (g₂ := g₂₇) hn5 (by decide) hA₇ hS₇
      (Equiv.Perm.mem_alternatingGroup.mpr (by decide))
      (Equiv.Perm.mem_alternatingGroup.mpr (by decide)) hC hG hβ

end CFSG.ClassicalInvolution.Q3.TL4
