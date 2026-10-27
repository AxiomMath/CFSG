module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem c25_ker_coprime (K A : Subgroup G) :
    Nat.Coprime 3 (Nat.card ↥(A.subgroupOf K ⊓
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).ker)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [QuotientGroup.ker_mk']
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    CFSG.pPrimeCore_coprime_card

theorem c25_core_le {K A : Subgroup G} (hAK : A ≤ K) :
    GLAPPrimeCoreOf 3 (barX 3 K A) ≤ barX 3 K (GLAPPrimeCoreOf 3 A) := by
  set ψ : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hψ
  set A₀ : Subgroup ↥K := A.subgroupOf K with hA₀
  have h1 := glaPPrimeCore_map_subgroupMap (p := 3) Nat.prime_three ψ A₀ (c25_ker_coprime K A)
  intro y hy
  obtain ⟨hyF, hy'⟩ := mem_glaPPrimeCoreOf_iff.1 hy
  have hy'' : (⟨y, hyF⟩ : ↥(Subgroup.map ψ A₀)) ∈ GLAPPrimeCore 3 ↥(Subgroup.map ψ A₀) := hy'
  rw [← h1] at hy''
  obtain ⟨a₀, ha₀, ha₀eq⟩ := hy''
  let e : ↥A₀ ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAK
  have h2 := glaPPrimeCore_map_iso 3 e
  have hea : e a₀ ∈ GLAPPrimeCore 3 ↥A := by
    rw [← h2]
    exact ⟨a₀, ha₀, rfl⟩
  have hmemA : ((a₀ : ↥K) : G) ∈ A := Subgroup.mem_subgroupOf.1 a₀.2
  have hmem : ((a₀ : ↥K) : G) ∈ GLAPPrimeCoreOf 3 A :=
    mem_glaPPrimeCoreOf_iff.2 ⟨hmemA, hea⟩
  refine ⟨(a₀ : ↥K), Subgroup.mem_subgroupOf.2 hmem, ?_⟩
  have := congrArg Subtype.val ha₀eq
  exact this

theorem c25_layer_le {K A : Subgroup G} (hAK : A ≤ K) :
    GLAPLayer 3 (barX 3 K A) ≤ barX 3 K (GLAPLayer 3 A) := by
  set ψ : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hψ
  set A₀ : Subgroup ↥K := A.subgroupOf K with hA₀
  refine sSup_le fun L hL => ?_
  obtain ⟨K₀, hK₀, hK₀map⟩ := exists_glaPComponent_map_eq (p := 3) Nat.prime_three ψ
    (A := A₀) (c25_ker_coprime K A) hL
  have hker2 : Nat.Coprime 3 (Nat.card ↥(A₀ ⊓ K.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hK1 := glaPComponent_map Nat.prime_three K.subtype hker2 hK₀
  rw [hA₀, Subgroup.map_subgroupOf_eq_of_le hAK] at hK1
  have hle : K₀.map K.subtype ≤ GLAPLayer 3 A := le_sSup hK1
  have hsub : (K₀.map K.subtype).subgroupOf K = K₀ :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective K₀
  have : barX 3 K (K₀.map K.subtype) = L := by
    show ((K₀.map K.subtype).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) = L
    rw [hsub]
    exact hK₀map
  rw [← this]
  exact barX_mono 3 hle

end CFSG.HardMathSupport.Solomon.Coordinator
