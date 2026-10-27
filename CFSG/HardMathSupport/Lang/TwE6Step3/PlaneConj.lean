module

public import CFSG.Assembly.Defs
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Open CFSG.LieType.SeitzGeneration
open scoped Pointwise

theorem exists_conj_le_of_rank_le {C : Type*} [Group C] [Finite C] {p : ℕ} [hp : Fact p.Prime]
    (hcomm : ∀ Q : Subgroup C, IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hrank : ∀ F : Subgroup C, IsElemAbelian p F → Nat.card F ≤ p ^ 3)
    {E F : Subgroup C} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hF : IsElemAbelian p F) :
    ∃ c : C, F.map (MulAut.conj c).toMonoidHom ≤ E := by
  classical
  have hpg : ∀ {Q : Subgroup C}, IsElemAbelian p Q → IsPGroup p Q := fun {Q} hQ x =>
    ⟨1, by
      apply Subtype.ext
      simpa using hQ.2 x x.2⟩
  obtain ⟨S, hS⟩ := (hpg hF).exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := (hpg hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S S₀
  have hSab : ∀ a ∈ (S₀ : Subgroup C), ∀ b ∈ (S₀ : Subgroup C), a * b = b * a :=
    hcomm S₀ S₀.isPGroup'
  set F' : Subgroup C := F.map (MulAut.conj g).toMonoidHom with hF'
  have hF'S : F' ≤ S₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x ∈ (S : Subgroup C) := hS hx
    have h2 : g * x * g⁻¹ ∈ ((g • S : Sylow p C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx0, by simp [MulAut.smul_def]⟩
    rw [hg] at h2
    exact h2
  let Ω : Subgroup C :=
    { carrier := {x | x ∈ (S₀ : Subgroup C) ∧ x ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hSab a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩ : IsElemAbelian p Ω :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hSab a a.2.1 b b.2.1), fun x hx => hx.2⟩
  have hEΩ : E ≤ Ω := fun x hx => ⟨hS₀ hx, hE.2 x hx⟩
  have hF'Ω : F' ≤ Ω := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hF'S ⟨x, hx, rfl⟩, ?_⟩
    rw [← map_pow, hF.2 x hx, map_one]
  have hΩc : Nat.card Ω ≤ Nat.card E := by
    rw [hEc]
    exact hrank Ω hΩ
  have hEq : E = Ω := Subgroup.eq_of_le_of_card_ge hEΩ hΩc
  exact ⟨g, hEq ▸ hF'Ω⟩

theorem exists_plane_le_cube_inf {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hcomm : ∀ Q : Subgroup G, IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hrank : ∀ F : Subgroup G, IsElemAbelian p F → Nat.card F ≤ p ^ 3)
    {E Y F : Subgroup G} {y : G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hy : y ∈ E)
    (hYy : ∀ g ∈ Y, g * y = y * g)
    (hYn : ∀ c : G, c * y = y * c → ∀ x ∈ Y, c * x * c⁻¹ ∈ Y)
    (hF : IsElemAbelian p F) (hFc : Nat.card F = p ^ 2) (hFY : F ≤ Y) :
    ∃ E' : Subgroup G, E' ≤ E ∧ E' ≤ Y ∧ IsElemAbelian p E' ∧ Nat.card E' = p ^ 2 := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  have hmemC : ∀ x : G, x ∈ C ↔ x * y = y * x := fun x => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hEC : E ≤ C := fun x hx => (hmemC x).2 (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩ |> fun h =>
    congrArg Subtype.val h)
  have hFC : F ≤ C := fun x hx => (hmemC x).2 (hYy x (hFY hx))
  set Ec : Subgroup C := E.subgroupOf C with hEcdef
  set Fc : Subgroup C := F.subgroupOf C with hFcdef
  have hmapE : Ec.map C.subtype = E := by
    rw [hEcdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hEC]
  have hmapF : Fc.map C.subtype = F := by
    rw [hFcdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hFC]
  have hcardmap : ∀ Q : Subgroup C, Nat.card (Q.map C.subtype) = Nat.card Q := fun Q =>
    Subgroup.card_map_of_injective (Subgroup.subtype_injective C)
  have hEcard : Nat.card Ec = p ^ 3 := by
    rw [← hcardmap, hmapE, hEc]
  have hEcE : IsElemAbelian p Ec := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
    · have ha : (a : G) ∈ E := by
        have : (a : G) ∈ Ec.map C.subtype := ⟨a, a.2, rfl⟩
        rwa [hmapE] at this
      have hb : (b : G) ∈ E := by
        have : (b : G) ∈ Ec.map C.subtype := ⟨b, b.2, rfl⟩
        rwa [hmapE] at this
      have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · have hx' : (x : G) ∈ E := by
        have : (x : G) ∈ Ec.map C.subtype := ⟨x, hx, rfl⟩
        rwa [hmapE] at this
      exact Subtype.ext (by simpa using hE.2 _ hx')
  have hFcF : IsElemAbelian p Fc := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
    · have ha : (a : G) ∈ F := by
        have : (a : G) ∈ Fc.map C.subtype := ⟨a, a.2, rfl⟩
        rwa [hmapF] at this
      have hb : (b : G) ∈ F := by
        have : (b : G) ∈ Fc.map C.subtype := ⟨b, b.2, rfl⟩
        rwa [hmapF] at this
      have h := congrArg Subtype.val (hF.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · have hx' : (x : G) ∈ F := by
        have : (x : G) ∈ Fc.map C.subtype := ⟨x, hx, rfl⟩
        rwa [hmapF] at this
      exact Subtype.ext (by simpa using hF.2 _ hx')
  have hcommC : ∀ Q : Subgroup C, IsPGroup p Q → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro Q hQ a ha b hb
    have hQ' : IsPGroup p (Q.map C.subtype) := hQ.map C.subtype
    exact Subtype.ext (hcomm _ hQ' _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  have hrankC : ∀ Q : Subgroup C, IsElemAbelian p Q → Nat.card Q ≤ p ^ 3 := by
    intro Q hQ
    have hQ' : IsElemAbelian p (Q.map C.subtype) := by
      refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
      · obtain ⟨a', ha', ha⟩ := a.2
        obtain ⟨b', hb', hb⟩ := b.2
        apply Subtype.ext
        change (a : G) * b = b * a
        rw [← ha, ← hb]
        exact congrArg (fun z : Q => ((z : C) : G)) (hQ.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      · rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hQ.2 x hx)
    rw [← hcardmap]
    exact hrank _ hQ'
  obtain ⟨c, hc⟩ := exists_conj_le_of_rank_le hcommC hrankC hEcE hEcard hFcF
  refine ⟨((F.subgroupOf C).map (MulAut.conj c).toMonoidHom).map C.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hc hx
    have h2 : (x : G) ∈ Ec.map C.subtype := ⟨x, this, rfl⟩
    rwa [hmapE] at h2
  · rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    have hzF : (z : G) ∈ F := by
      have : (z : G) ∈ Fc.map C.subtype := ⟨z, hz, rfl⟩
      rwa [hmapF] at this
    have h1 := hYn (c : G) ((hmemC _).1 c.2) _ (hFY hzF)
    simpa using h1
  · refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
    · obtain ⟨a', ⟨a'', ha'', rfl⟩, ha⟩ := a.2
      obtain ⟨b', ⟨b'', hb'', rfl⟩, hb⟩ := b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← ha, ← hb]
      have hcm := hFcF.1.is_comm.comm ⟨a'', ha''⟩ ⟨b'', hb''⟩
      have hcm' : a'' * b'' = b'' * a'' := congrArg Subtype.val hcm
      change ((c * a'' * c⁻¹ : C) : G) * ((c * b'' * c⁻¹ : C) : G) =
        ((c * b'' * c⁻¹ : C) : G) * ((c * a'' * c⁻¹ : C) : G)
      have e : c * a'' * c⁻¹ * (c * b'' * c⁻¹) = c * b'' * c⁻¹ * (c * a'' * c⁻¹) := by
        calc c * a'' * c⁻¹ * (c * b'' * c⁻¹) = c * (a'' * b'') * c⁻¹ := by group
          _ = c * (b'' * a'') * c⁻¹ := by rw [hcm']
          _ = c * b'' * c⁻¹ * (c * a'' * c⁻¹) := by group
      exact congrArg (fun z : C => (z : G)) e
    · rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := hFcF.2 z hz
      have : (MulAut.conj c).toMonoidHom z ^ p = 1 := by
        rw [← map_pow, h1, map_one]
      simpa using congrArg Subtype.val this
  · rw [hcardmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    rw [← hFc, ← hcardmap, hmapF]

end CFSG.HardMathSupport.Lang.TwE6Step3
