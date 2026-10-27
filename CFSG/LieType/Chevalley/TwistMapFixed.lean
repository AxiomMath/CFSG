module

public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem twistedFixedGroup_le_adjointGroup : twistedFixedGroup t K σ ≤ adjointGroup t.tag K :=
  inf_le_left

theorem coe_mem_twistedFixedGroup_iff (g : adjointGroup t.tag K) :
    (g : ModGL t.tag K) ∈ twistedFixedGroup t K σ ↔ twistC t K σ g = g :=
  ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩

theorem mem_twistedFixedGroup_iff {g : ModGL t.tag K} :
    g ∈ twistedFixedGroup t K σ ↔
      ∃ x : adjointGroup t.tag K, twistC t K σ x = x ∧ (x : ModGL t.tag K) = g :=
  ⟨fun h => ⟨⟨g, h.1⟩, (coe_mem_twistedFixedGroup_iff t K σ ⟨g, h.1⟩).1 h, rfl⟩,
    fun ⟨x, hx, hxg⟩ => hxg ▸ (coe_mem_twistedFixedGroup_iff t K σ x).2 hx⟩

theorem twistedFixedGroup_eq_map :
    twistedFixedGroup t K σ =
      (MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _)).map (adjointGroup t.tag K).subtype := by
  ext g
  rw [mem_twistedFixedGroup_iff]
  exact ⟨fun ⟨x, hx, hxg⟩ => ⟨x, hx, hxg⟩, fun ⟨x, hx, hxg⟩ => ⟨x, hx, hxg⟩⟩

theorem twistedFixedGroup_subgroupOf :
    (twistedFixedGroup t K σ).subgroupOf (adjointGroup t.tag K) =
      MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _) := by
  ext g
  rw [Subgroup.mem_subgroupOf, coe_mem_twistedFixedGroup_iff]
  rfl

@[expose] noncomputable def twistedFixedGroupEquiv :
    twistedFixedGroup t K σ ≃* MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _) :=
  ((Subgroup.equivMapOfInjective _ (adjointGroup t.tag K).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (twistedFixedGroup_eq_map t K σ).symm)).symm

theorem coe_twistedFixedGroupEquiv (g : twistedFixedGroup t K σ) :
    ((twistedFixedGroupEquiv t K σ g : adjointGroup t.tag K) : ModGL t.tag K) = g := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨x, hx, rfl⟩ := (mem_twistedFixedGroup_iff t K σ).1 hg
  have h : twistedFixedGroupEquiv t K σ ⟨x, hg⟩ = ⟨x, hx⟩ := by
    rw [twistedFixedGroupEquiv, MulEquiv.symm_apply_eq]
    rfl
  rw [h]

end CFSG.LieType.Chevalley
