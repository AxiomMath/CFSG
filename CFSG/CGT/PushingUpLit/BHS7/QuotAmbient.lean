module

public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixQuot

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.LieType.BorelTits CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

section Finite

variable [Finite Γ]

theorem opResidual_autOn {G V : Subgroup Γ} (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) :
    opResidual 2 (autOn G V) = autOn (opResidual 2 G) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine opResidual_le_of_pow_mem fun x hx => ?_
    obtain ⟨a, haG, rfl⟩ := mem_autOn_iff.mp hx
    obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := 2) (A := G) haG
    refine ⟨k, mem_autOn_iff.mpr ⟨a ^ 2 ^ k, ?_, ?_⟩⟩
    · simpa using hk
    · simp
  · intro x hx
    obtain ⟨a, haO, rfl⟩ := mem_autOn_iff.mp hx
    have key : ∀ g ∈ opResidual 2 G, ∀ hg : g ∈ Subgroup.normalizer (V : Set Γ),
        conjAct V ⟨g, hg⟩ ∈ opResidual 2 (autOn G V) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        intro hxN
        refine mem_opResidual_of_coprime (mem_autOn_iff.mpr ⟨⟨x, hxN⟩, hx.1, rfl⟩) ?_
        refine Nat.Coprime.coprime_dvd_left ?_ hx.2
        have h1 := orderOf_map_dvd (conjAct V) (⟨x, hxN⟩ : Subgroup.normalizer (V : Set Γ))
        rwa [Subgroup.orderOf_mk] at h1
      | one =>
        intro _
        have : (⟨1, _⟩ : Subgroup.normalizer (V : Set Γ)) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        intro hxy
        have hxN : x ∈ Subgroup.normalizer (V : Set Γ) := hGV (opResidual_le 2 G hx)
        have hyN : y ∈ Subgroup.normalizer (V : Set Γ) := hGV (opResidual_le 2 G hy)
        have : (⟨x * y, hxy⟩ : Subgroup.normalizer (V : Set Γ)) = ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
        rw [this, map_mul]
        exact Subgroup.mul_mem _ (ihx hxN) (ihy hyN)
      | inv x hx ih =>
        intro hxN
        have hxN' : x ∈ Subgroup.normalizer (V : Set Γ) := hGV (opResidual_le 2 G hx)
        have : (⟨x⁻¹, hxN⟩ : Subgroup.normalizer (V : Set Γ)) = (⟨x, hxN'⟩)⁻¹ := rfl
        rw [this, map_inv]
        exact Subgroup.inv_mem _ (ih hxN')
    exact key a haO a.2

theorem fixOp_autOn_eq {G V : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) :
    @BHS5.fixOp ↥V (commGroupOfElemAbelian hV) (autOn G V) =
      (Subgroup.centralizer (opResidual 2 G : Set Γ)).subgroupOf V := by
  have h1 : @BHS5.fixOp ↥V (commGroupOfElemAbelian hV) (autOn G V) =
      @fixV ↥V (commGroupOfElemAbelian hV) (autOn (opResidual 2 G) V) := by
    unfold BHS5.fixOp
    rw [opResidual_autOn hGV]
  rw [h1]
  exact fixOn_eq hV ((opResidual_le 2 G).trans hGV)

theorem pCoreOf_autOn_vSub_eq_bot {G T : Subgroup Γ} (hT : IsSylowTwoOf T G) :
    pCoreOf 2 (autOn G (vSub G T)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup Γ := vSub G T with hVdef
  have hGV : G ≤ Subgroup.normalizer (V : Set Γ) := le_normalizer_vSub G T
  set N : Subgroup (MulAut ↥V) := pCoreOf 2 (autOn G V) with hN
  have hNK : N ≤ autOn G V := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  set R : Subgroup Γ :=
    G ⊓ (N.comap (conjAct V)).map (Subgroup.normalizer (V : Set Γ)).subtype with hR
  have hmemR : ∀ g : Γ, g ∈ R ↔ g ∈ G ∧ ∃ h : g ∈ Subgroup.normalizer (V : Set Γ),
      conjAct V ⟨g, h⟩ ∈ N := by
    intro g
    rw [hR, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hg, ⟨y, hy, rfl⟩⟩
      exact ⟨hg, y.2, hy⟩
    · rintro ⟨hg, h, hh⟩
      exact ⟨hg, ⟨⟨g, h⟩, hh, rfl⟩⟩
  have hRG : R ≤ G := inf_le_left
  have key : ∀ g ∈ G, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    obtain ⟨hrG, hrN, hrc⟩ := (hmemR r).mp hr
    refine (hmemR _).mpr ⟨G.mul_mem (G.mul_mem hg hrG) (G.inv_mem hg), ?_⟩
    have hgN : g ∈ Subgroup.normalizer (V : Set Γ) := hGV hg
    have hgrN : g * r * g⁻¹ ∈ Subgroup.normalizer (V : Set Γ) :=
      (Subgroup.normalizer (V : Set Γ)).mul_mem
        ((Subgroup.normalizer (V : Set Γ)).mul_mem hgN hrN)
        ((Subgroup.normalizer (V : Set Γ)).inv_mem hgN)
    refine ⟨hgrN, ?_⟩
    have h1 : (⟨g * r * g⁻¹, hgrN⟩ : Subgroup.normalizer (V : Set Γ)) =
        ⟨g, hgN⟩ * ⟨r, hrN⟩ * (⟨g, hgN⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    have hgK : conjAct V ⟨g, hgN⟩ ∈ autOn G V := mem_autOn_iff.mpr ⟨⟨g, hgN⟩, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_self _ hgK) _).mp hrc
  have hRn : G ≤ Subgroup.normalizer (R : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun h => key g hg r h, fun h => ?_⟩
    have h2 := key g⁻¹ (G.inv_mem hg) _ h
    have e : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
    rwa [e] at h2
  have hR2 : IsPGroup 2 ↥(autOn R V) := by
    have hle : autOn R V ≤ N := by
      intro x hx
      obtain ⟨a, haR, rfl⟩ := mem_autOn_iff.mp hx
      obtain ⟨-, hN', hc⟩ := (hmemR a).mp haR
      exact hc
    exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _).to_le hle
  have hRC : R ≤ Subgroup.centralizer (V : Set Γ) :=
    le_centralizer_vSub_of_isPGroup_autOn hT hRG hRn hR2
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨a, haG, rfl⟩ := mem_autOn_iff.mp (hNK hn)
  have haR : (a : Γ) ∈ R := (hmemR a).mpr ⟨haG, a.2, hn⟩
  rw [Subgroup.mem_bot]
  exact (conjAct_eq_one_iff V a).mpr (hRC haR)

end Finite

end CFSG.CGT.PushingUpLit.BHS7
