module

public import CFSG.CGT.PushingUpLit.A78G0.Sides
public import CFSG.CGT.PushingUpLit.A78.Sp4Transport

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools

section Generic

variable {G : Type} [Group G]

theorem sq_of_sup_commuting {B C : Subgroup G} (hB : ∀ x ∈ B, x * x = 1)
    (hC : ∀ x ∈ C, x * x = 1) (hBC : Commuting B C) : ∀ x ∈ C ⊔ B, x * x = 1 := by
  intro x hx
  obtain ⟨c, hc, b, hb, rfl⟩ := (mem_sup_iff_of_normalizes (K := C) (H := B)
    (fun b hb c hc => by
      have : b * c * b⁻¹ = c := by rw [(hBC b hb c hc).eq]; group
      rw [this]
      exact hc)).1 hx
  have hbc : b * c = c * b := (hBC b hb c hc).eq
  calc c * b * (c * b) = c * (b * c) * b := by group
    _ = c * (c * b) * b := by rw [hbc]
    _ = (c * c) * (b * b) := by group
    _ = 1 := by rw [hC c hc, hB b hb, one_mul]

theorem cs_mem_zClass {Z B : Subgroup G} (hB : B ∈ zClass Z) (g : G) : cs B g ∈ zClass Z :=
  A78.conjSub_mem_zClass hB g

end Generic

@[expose] def lines {G : Type} [Group G] (V W : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ m ∈ Subgroup.normalizer (V : Set G), U = cs W m}

@[expose] def cliq {G : Type} [Group G] (Z U : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ zClass Z ∧ B ≠ Z ∧ B ≤ U}

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem elemAb2_Z : ElemAb2 Z := h.elemAb2_V.mono h.Z_le_V

theorem normalizer_Z_eq : Subgroup.normalizer (Z : Set G) = Subgroup.normalizer (V : Set G) :=
  h.side₁.normalizer_Z

theorem cs_Z_of_mem {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G)) : cs Z m = Z :=
  cs_of_mem_normalizer (h.normalizer_Z_eq ▸ hm)

theorem le_M_of_commuting {C : Subgroup G} (hC : Commuting Z C) :
    C ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨z, hz, hz1⟩ := h.ex_ne_one_Z
  intro c hc
  apply h.side₁.cent_z z hz hz1
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hC z hz c hc).eq.symm

theorem elemAb2_of_mem_zClass {B : Subgroup G} (hB : B ∈ zClass Z) : ElemAb2 B := by
  obtain ⟨g, rfl⟩ := hB
  exact elemAb2_cj h.elemAb2_Z g

theorem exists_clique {B C : Subgroup G} (hB : B ∈ zClass Z) (hBZ : B ≠ Z)
    (hBM : B ≤ Subgroup.normalizer (V : Set G)) (hC : ElemAb2 C)
    (hCM : C ≤ Subgroup.normalizer (V : Set G)) (hBC : Commuting B C) :
    ∃ U ∈ lines V W, B ≤ U ∧ C ≤ U := by
  have hB2 := h.elemAb2_of_mem_zClass hB
  obtain ⟨g, hg⟩ := hB
  have hg' : B = cs Z g := hg.symm
  subst hg'
  have hsq : ∀ x ∈ C ⊔ cs Z g, x * x = 1 :=
    sq_of_sup_commuting (fun x hx => (hB2 x hx x hx).2) (fun x hx => (hC x hx x hx).2) hBC
  have hE2 : IsPGroup 2 ↥(C ⊔ cs Z g) := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have := hsq x x.2
    simpa [pow_two] using this
  have hEM : C ⊔ cs Z g ≤ Subgroup.normalizer (V : Set G) := sup_le hCM hBM
  obtain ⟨k, hk, hkE⟩ := exists_conj_le_of_isSylowOf h.side₁.sylow_T hEM hE2
  have hsq' : ∀ x ∈ cs (C ⊔ cs Z g) k, x * x = 1 := sq_of_mem_conjSub hsq k
  rcases h.jst.elemAbelian_le hkE hsq' with h1 | h1
  ·
    exfalso
    have hBk : cs (cs Z g) k ≤ V := fun x hx =>
      h1 (cs_mono (le_sup_right : cs Z g ≤ C ⊔ cs Z g) k hx)
    have hBk' : cs Z (k * g) = Z := h.eq_of_cs_le_V (by rw [cs_mul]; exact hBk)
    rw [cs_mul] at hBk'
    apply hBZ
    have := cs_cs_inv (cs Z g) k
    rw [hBk'] at this
    rw [← this]
    exact h.cs_Z_of_mem ((Subgroup.normalizer (V : Set G)).inv_mem hk)
  · refine ⟨cs W k⁻¹, ⟨k⁻¹, (Subgroup.normalizer (V : Set G)).inv_mem hk, rfl⟩, ?_, ?_⟩
    · intro x hx
      rw [mem_cs, inv_inv]
      exact h1 (conj_mem_cs k ((le_sup_right : cs Z g ≤ C ⊔ cs Z g) hx))
    · intro x hx
      rw [mem_cs, inv_inv]
      exact h1 (conj_mem_cs k ((le_sup_left : C ≤ C ⊔ cs Z g) hx))

theorem cs_W_eq_of_cs_J_eq {m m' : G} (hJ : cs (V ⊔ W) m = cs (V ⊔ W) m') : cs W m = cs W m' := by
  have h1 : cs (V ⊔ W) (m⁻¹ * m') = V ⊔ W := by
    rw [cs_mul, ← hJ, cs_cs_inv]
  have h2 : m⁻¹ * m' ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) :=
    mem_normalizer_of_cs_eq h1
  have h3 : cs W (m⁻¹ * m') = W := cs_of_mem_normalizer (h.normalizer_J_le_W h2)
  have h4 : cs W m' = cs W m :=
    calc cs W m' = cs W (m * (m⁻¹ * m')) := by rw [mul_inv_cancel_left]
      _ = cs (cs W (m⁻¹ * m')) m := cs_mul _ _ _
      _ = cs W m := by rw [h3]
  exact h4.symm

theorem unique_clique {B : Subgroup G} (hB : B ∈ zClass Z) (hBZ : B ≠ Z) {m m' : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) (hm' : m' ∈ Subgroup.normalizer (V : Set G))
    (hBU : B ≤ cs W m) (hBU' : B ≤ cs W m') : cs W m = cs W m' := by
  by_contra hne
  have hne' : cs (V ⊔ W) m ≠ cs (V ⊔ W) m' := fun hJ => hne (h.cs_W_eq_of_cs_J_eq hJ)
  have hinf := h.inf_cs_J_le_V hm hm' hne'
  have hBV : B ≤ V := fun x hx =>
    hinf ⟨cs_mono le_sup_right m (hBU hx), cs_mono le_sup_right m' (hBU' hx)⟩
  obtain ⟨g, rfl⟩ := hB
  exact hBZ (h.eq_of_cs_le_V (g := g) hBV)

theorem Z_le_cs_W {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G)) : Z ≤ cs W m := by
  have := cs_mono h.Z_le_W m
  rwa [h.cs_Z_of_mem hm] at this

theorem cliq_cs {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    cliq Z (cs W m) = (fun B => cs B m) '' cliq Z W := by
  ext B
  constructor
  · rintro ⟨hBΔ, hBZ, hBU⟩
    refine ⟨cs B m⁻¹, ⟨cs_mem_zClass hBΔ m⁻¹, ?_, ?_⟩, cs_inv_cs B m⟩
    · intro hZ'
      apply hBZ
      have := cs_inv_cs B m
      rw [hZ'] at this
      rw [← this]
      exact h.cs_Z_of_mem hm
    · have := cs_mono hBU m⁻¹
      rwa [cs_cs_inv] at this
  · rintro ⟨B', ⟨hBΔ, hBZ, hBU⟩, rfl⟩
    refine ⟨cs_mem_zClass hBΔ m, ?_, cs_mono hBU m⟩
    intro hZ'
    apply hBZ
    have hZ'' : cs B' m = Z := hZ'
    have := cs_cs_inv B' m
    rw [hZ''] at this
    rw [← this]
    exact h.cs_Z_of_mem ((Subgroup.normalizer (V : Set G)).inv_mem hm)

theorem ncard_cliq_W : (cliq Z W).ncard = 2 ^ e := by
  have hset : cliq Z W = {B : Subgroup G | ∃ n ∈ Subgroup.normalizer (W : Set G), B = cs Z n} \
      ({Z} : Set (Subgroup G)) := by
    ext B
    constructor
    · rintro ⟨hBΔ, hBZ, hBW⟩
      obtain ⟨g, rfl⟩ := hBΔ
      obtain ⟨n, hn, hgn⟩ := h.exists_normalizer_of_cs_le_W (g := g) hBW
      exact ⟨⟨n, hn, hgn⟩, hBZ⟩
    · rintro ⟨⟨n, hn, rfl⟩, hBZ⟩
      exact ⟨⟨n, rfl⟩, hBZ, h.cs_le_W_of_mem hn⟩
  have hmem : Z ∈ {B : Subgroup G | ∃ n ∈ Subgroup.normalizer (W : Set G), B = cs Z n} :=
    ⟨1, Subgroup.one_mem _, (cs_one Z).symm⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem hmem, h.ncard_conj_Z₂]
  simp

theorem ncard_cliq {U : Subgroup G} (hU : U ∈ lines V W) : (cliq Z U).ncard = 2 ^ e := by
  obtain ⟨m, hm, rfl⟩ := hU
  rw [h.cliq_cs hm, Set.ncard_image_of_injective _ (fun B B' hBB => (cs_inj_iff m).1 hBB)]
  exact h.ncard_cliq_W

theorem mem_sigma_iff {B : Subgroup G} :
    B ∈ sigmaSet (zClass Z) Z ↔ ∃ U ∈ lines V W, B ∈ cliq Z U := by
  constructor
  · rintro ⟨hB, hBZ, hcomm⟩
    have hBM : B ≤ Subgroup.normalizer (V : Set G) := h.le_M_of_commuting hcomm
    have hB2 := h.elemAb2_of_mem_zClass hB
    obtain ⟨U, hU, hBU, -⟩ := h.exists_clique hB hBZ hBM hB2 hBM
      (fun x hx y hy => (hB2 x hx y hy).1)
    exact ⟨U, hU, hB, hBZ, hBU⟩
  · rintro ⟨U, ⟨m, hm, rfl⟩, hB, hBZ, hBU⟩
    exact ⟨hB, hBZ, fun z hz b hb =>
      commute_of_mem_conjSub h.jst.abelian_V₂ m z (h.Z_le_cs_W hm hz) b (hBU hb)⟩

theorem sigma_comm_iff {B C U : Subgroup G} (hB : B ∈ sigmaSet (zClass Z) Z)
    (hU : U ∈ lines V W) (hBU : B ≤ U) :
    (C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C) ↔ C ∈ cliq Z U := by
  obtain ⟨m, hm, rfl⟩ := hU
  constructor
  · rintro ⟨hC, hBC⟩
    obtain ⟨hCΔ, hCZ, hCcomm⟩ := hC
    have hBM := h.le_M_of_commuting hB.2.2
    have hCM := h.le_M_of_commuting hCcomm
    obtain ⟨U', ⟨m', hm', rfl⟩, hBU', hCU'⟩ :=
      h.exists_clique hB.1 hB.2.1 hBM (h.elemAb2_of_mem_zClass hCΔ) hCM hBC
    have h1 := h.unique_clique hB.1 hB.2.1 hm hm' hBU hBU'
    refine ⟨hCΔ, hCZ, ?_⟩
    rw [h1]
    exact hCU'
  · rintro ⟨hCΔ, hCZ, hCU⟩
    refine ⟨(h.mem_sigma_iff).2 ⟨_, ⟨m, hm, rfl⟩, hCΔ, hCZ, hCU⟩, ?_⟩
    exact fun b hb c hc => commute_of_mem_conjSub h.jst.abelian_V₂ m b (hBU hb) c (hCU hc)

theorem sigma_trans : ∀ B ∈ sigmaSet (zClass Z) Z, ∀ C ∈ sigmaSet (zClass Z) Z,
    ∀ D ∈ sigmaSet (zClass Z) Z, Commuting B C → Commuting C D → Commuting B D := by
  intro B hB C hC D hD hBC hCD
  obtain ⟨U, hU, hBU⟩ := (h.mem_sigma_iff).1 hB
  have hCU : C ∈ cliq Z U := (h.sigma_comm_iff hB hU hBU.2.2).1 ⟨hC, hBC⟩
  have hDU : D ∈ cliq Z U := (h.sigma_comm_iff hC hU hCU.2.2).1 ⟨hD, hCD⟩
  obtain ⟨m, hm, rfl⟩ := hU
  exact fun b hb d hd => commute_of_mem_conjSub h.jst.abelian_V₂ m b (hBU.2.2 hb) d (hDU.2.2 hd)

theorem sigma_clique : ∀ B ∈ sigmaSet (zClass Z) Z,
    Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C} = 2 ^ e := by
  intro B hB
  obtain ⟨U, hU, hBU⟩ := (h.mem_sigma_iff).1 hB
  have h1 : Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C} =
      Nat.card {C : Subgroup G // C ∈ cliq Z U} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun C => h.sigma_comm_iff hB hU hBU.2.2)
  rw [h1, Nat.card_coe_set_eq]
  exact h.ncard_cliq hU

theorem sigma_card : Nat.card (sigmaSet (zClass Z) Z) = 2 ^ e * (2 ^ e + 1) := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  let 𝒰 : Finset (Subgroup G) := Finset.univ.filter (fun U => U ∈ lines V W)
  let K : Subgroup G → Finset (Subgroup G) :=
    fun U => Finset.univ.filter (fun B => B ∈ cliq Z U)
  have hK : ∀ U, ((K U : Finset (Subgroup G)) : Set (Subgroup G)) = cliq Z U := fun U => by
    ext B
    simp [K]
  have h𝒰 : ((𝒰 : Finset (Subgroup G)) : Set (Subgroup G)) = lines V W := by
    ext U
    simp [𝒰]
  have hS : sigmaSet (zClass Z) Z = ((𝒰.biUnion K : Finset (Subgroup G)) : Set (Subgroup G)) := by
    ext B
    rw [Finset.mem_coe, Finset.mem_biUnion]
    constructor
    · intro hB
      obtain ⟨U, hU, hBU⟩ := (h.mem_sigma_iff).1 hB
      exact ⟨U, by simpa [𝒰] using hU, by simpa [K] using hBU⟩
    · rintro ⟨U, hU, hBU⟩
      exact (h.mem_sigma_iff).2 ⟨U, by simpa [𝒰] using hU, by simpa [K] using hBU⟩
  have hdisj : ∀ U ∈ 𝒰, ∀ U' ∈ 𝒰, U ≠ U' → Disjoint (K U) (K U') := by
    intro U hU U' hU' hne
    rw [Finset.disjoint_left]
    intro B hB hB'
    have hU1 : U ∈ lines V W := by simpa [𝒰] using hU
    have hU2 : U' ∈ lines V W := by simpa [𝒰] using hU'
    have hB1 : B ∈ cliq Z U := by simpa [K] using hB
    have hB2 : B ∈ cliq Z U' := by simpa [K] using hB'
    obtain ⟨m, hm, rfl⟩ := hU1
    obtain ⟨m', hm', rfl⟩ := hU2
    exact hne (h.unique_clique hB1.1 hB1.2.1 hm hm' hB1.2.2 hB2.2.2)
  have hcardK : ∀ U ∈ 𝒰, (K U).card = 2 ^ e := by
    intro U hU
    have hU1 : U ∈ lines V W := by simpa [𝒰] using hU
    rw [← Set.ncard_coe_finset, hK]
    exact h.ncard_cliq hU1
  have hcard𝒰 : 𝒰.card = 2 ^ e + 1 := by
    rw [← Set.ncard_coe_finset, h𝒰]
    exact h.ncard_conj_W
  rw [Nat.card_coe_set_eq, hS, Set.ncard_coe_finset, Finset.card_biUnion hdisj,
    Finset.sum_const_nat hcardK, hcard𝒰]
  ring

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
