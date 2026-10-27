module

public import CFSG.LieType.Chevalley.FixedNative
public import CFSG.LieType.Chevalley.FixedCollection
public import CFSG.LieType.Ree.RelWeylRee
public import CFSG.LieType.Ree.ReeUnipotent
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

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.BorelTits.Weighted ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

@[expose] noncomputable def reeFixed : Subgroup (adjointGroup t.tag K) :=
  MonoidHom.eqLocus (t.reeAut K a).toMonoidHom (MonoidHom.id _)

theorem mem_reeFixed {g : adjointGroup t.tag K} : g ∈ reeFixed t K a ↔ t.reeAut K a g = g :=
  Iff.rfl

theorem reeFixedGroup_eq_map_reeFixed :
    reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) =
      (reeFixed t K a).map (adjointGroup t.tag K).subtype :=
  (exceptional_reeFixedGroup_eq t K a).2.2

theorem reeFixed_bruhat :
    ∀ g ∈ reeFixed t K a, ∃ w ∈ t.relWeylRee, ∃ b₁ ∈ (nativeData t.tag K).B,
      b₁ ∈ reeFixed t K a ∧ ∃ b₂ ∈ (nativeData t.tag K).B, b₂ ∈ reeFixed t K a ∧
        g = b₁ * nrep t.tag K w * b₂ := by
  intro g hg
  obtain ⟨-, hdisj, hexists, hunique⟩ := native_refined_bruhat t.tag K
  obtain ⟨w, hw, b, hb, hbF, u, hu, huF, rfl⟩ := exists_reeFixed_mul a hdisj hexists hunique hg
  exact ⟨w, hw, b, hb, hbF, u, RootGroupData.U_le_B (Uminus_le_U t.tag K w hu), huF, rfl⟩

theorem nrep_mem_reeFixed {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    nrep t.tag K w ∈ reeFixed t K a := by
  rw [mem_reeFixed, reeAut_nrep, (mem_relWeylRee t).1 hw]

theorem reeFixed_hUw :
    ∀ w ∈ t.relWeylRee, w ≠ 1 → ∃ u ∈ (nativeData t.tag K).U, u ∈ reeFixed t K a ∧
      nrep t.tag K w * u * (nrep t.tag K w)⁻¹ ∉ (nativeData t.tag K).U := by
  intro w hw hw1
  obtain ⟨u, hu, hF, hn⟩ := exists_reeAut_fixed_conj_not_mem_U t K a hw hw1
  exact ⟨u, hu, hF, hn⟩

theorem holds_reeFixed : Holds (reeFixed t K a) t.prime :=
  holds_of_fixedNative t.prime (reeFixed t K a) t.relWeylRee (fixedSpace t.reeIsometry)
    t.reeVector t.inner_reeVector_pos t.reeVector_mem_fixedSpace
    (fun _ hw _ hx => t.weylAct_mem_fixedSpace_ree hw hx)
    (fun _ hw => nrep_mem_reeFixed t K a hw) (fun _ hv hfix => t.relWeylRee_fixfree hv hfix)
    (fun _ hx => t.relWeylRee_cover hx) (reeFixed_bruhat t K a) (reeFixed_hUw t K a)

theorem holds_reeFixedGroup :
    Holds (reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
      else t.prime ^ (a + 1))) t.prime := by
  rw [reeFixedGroup_eq_map_reeFixed]
  exact (holds_reeFixed t K a).of_mulEquiv
    ((reeFixed t K a).equivMapOfInjective _ (adjointGroup t.tag K).subtype_injective)

theorem exists_sylow_reeFixed :
    ∃ S : Sylow t.prime (reeFixed t K a), (S : Subgroup (reeFixed t K a)) =
      (nativeData t.tag K).U.comap (reeFixed t K a).subtype := by
  set F := nativeRootSubgroups t.tag K
  have hS₀p : IsPGroup t.prime ((nativeData t.tag K).U.comap (reeFixed t K a).subtype) :=
    (F.isPGroup_U t.prime).comap_of_injective _ Subtype.val_injective
  refine exists_sylow_eq_of_normalizer t.prime hS₀p fun g hg ⟨k, hk⟩ => ?_
  have hgB := normalizer_le_of_fixedData (nrep t.tag K) (nativeData t.tag K).B
    (nativeData t.tag K).U (reeFixed t K a) t.relWeylRee (reeFixed_bruhat t K a)
    F.B_le_normalizer_U (by rw [nrep_one]; exact one_mem _) (reeFixed_hUw t K a) hg
  exact F.mem_U_of_pow_eq_one t.prime hgB (k := k) (by simpa using congrArg Subtype.val hk)

end CFSG.LieType.Ree
