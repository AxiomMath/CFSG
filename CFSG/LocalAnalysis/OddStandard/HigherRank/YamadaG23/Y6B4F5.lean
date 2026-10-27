module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_F_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) {f m : G}
    (hf : f ∈ c.s.fr.F) (hm : m ∈ M3 c.s) : f * m = m * f := by
  haveI := y6e_M3_comm c hF
  exact Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s)
    ((le_sup_right : c.s.fr.F ≤ M3 c.s) hf) hm

private lemma y6b_g_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) {m : G}
    (hm : m ∈ M3 c.s) : c.g * m = m * c.g := by
  have hg := hF.2.2.2.1 hRT m hm
  have hgsq : c.g * c.g = 1 := y6b_g_sq c hRT
  have hgi : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hgsq
  rw [hgi] at hg
  calc c.g * m = (c.g * m * c.g) * c.g := by
        rw [mul_assoc (c.g * m) c.g c.g, hgsq, mul_one]
    _ = m * c.g := by rw [hg]

private lemma y6b_E16_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T)
    {e m : G} (he : e ∈ y6bE16 c) (hm : m ∈ M3 c.s) : e * m = m * e := by
  have hFc : c.s.fr.F ≤ Subgroup.centralizer (M3 c.s : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro m' hm'
    exact (y6b_F_comm_M3 c hF hf hm').symm
  have hgc : zpowers c.g ≤ Subgroup.centralizer (M3 c.s : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro m' hm'
    exact (y6b_g_comm_M3 c hF hRT hm').symm
  have hmem : e ∈ Subgroup.centralizer (M3 c.s : Set G) := (sup_le hFc hgc) he
  exact (Subgroup.mem_centralizer_iff.mp hmem m hm).symm

private lemma y6b_E_conj_M3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {e x : G} (he : e ∈ y6bE c.toCtx5) (hx : x ∈ M3 c.s) :
    e * x * e⁻¹ = x ∨ e * x * e⁻¹ = x⁻¹ := by
  have hdec : (∃ e₁ ∈ y6bE16 c.toCtx5, e = e₁) ∨
      (∃ e₁ ∈ y6bE16 c.toCtx5, e = e₁ * c.s.t) := by
    rw [y6b_mem_E c.toCtx5 hH hRT] at he
    obtain ⟨f, hf, h | h | h | h⟩ := he
    · exact Or.inl ⟨f, y6b_F_le_E16 c.toCtx5 hf, h⟩
    · exact Or.inl ⟨f * c.g, (y6bE16 c.toCtx5).mul_mem (y6b_F_le_E16 c.toCtx5 hf)
        (y6b_g_mem_E16 c.toCtx5), h⟩
    · exact Or.inr ⟨f, y6b_F_le_E16 c.toCtx5 hf, h⟩
    · exact Or.inr ⟨f * c.g, (y6bE16 c.toCtx5).mul_mem (y6b_F_le_E16 c.toCtx5 hf)
        (y6b_g_mem_E16 c.toCtx5), by rw [h]; group⟩
  rcases hdec with ⟨e₁, he₁, rfl⟩ | ⟨e₁, he₁, rfl⟩
  · left
    rw [y6b_E16_comm_M3 c.toCtx5 hF hRT he₁ hx]
    group
  · right
    have hc : Commute e₁ x := y6b_E16_comm_M3 c.toCtx5 hF hRT he₁ hx
    calc e₁ * c.s.t * x * (e₁ * c.s.t)⁻¹
        = e₁ * (c.s.t * x * c.s.t⁻¹) * e₁⁻¹ := by group
      _ = e₁ * x⁻¹ * e₁⁻¹ := by rw [y6b_t_inv_M3 c hH hF x hx]
      _ = x⁻¹ := by rw [hc.inv_right.eq]; group

private lemma y6b_W_conj_M3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {y x : G} (hy : y ∈ y6bW c.toCtx5) (hx : x ∈ M3 c.s) :
    y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
  rw [y6b_mem_W c.toCtx5 hH hF hRT] at hy
  obtain ⟨e, he, m, hm, rfl⟩ := hy
  haveI := y6e_M3_comm c.toCtx5 hF
  have hmc : Commute m x := Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hm hx
  have hkey : e * m * x * (e * m)⁻¹ = e * x * e⁻¹ := by
    rw [show e * m * x * (e * m)⁻¹ = e * (m * x * m⁻¹) * e⁻¹ by group]
    rw [show m * x * m⁻¹ = x by rw [hmc.eq]; group]
  rw [hkey]
  exact y6b_E_conj_M3 c hH hF hRT he hx

private def y6bTheta (c : Ctx6 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) (hRT : c.s.R ≠ c.s.T) {P : Subgroup G}
    (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) : ↥(M3 c.s) →* ↥(y6bE16 c.toCtx5) where
  toFun w := ⟨a * (w : G) * a⁻¹ * (w : G)⁻¹, by
    obtain ⟨e, he, hwe⟩ := y6b_a_conj_M3_E16 c hH hF hRT hP haP haF (w : G) w.2
    have h : a * (w : G) * a⁻¹ * (w : G)⁻¹ = e := by rw [hwe]; group
    rw [h]; exact he⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    obtain ⟨ey, hey, hyeq⟩ := y6b_a_conj_M3_E16 c hH hF hRT hP haP haF (y : G) y.2
    have hcomm : (a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G) =
        (x : G) * (a * (y : G) * a⁻¹ * (y : G)⁻¹) := by
      have hθy : a * (y : G) * a⁻¹ * (y : G)⁻¹ = ey := by rw [hyeq]; group
      rw [hθy]
      exact y6b_E16_comm_M3 c.toCtx5 hF hRT hey x.2
    have htx : (a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ =
        (x : G)⁻¹ * (a * (y : G) * a⁻¹ * (y : G)⁻¹) :=
      (show Commute (a * (y : G) * a⁻¹ * (y : G)⁻¹) (x : G) from hcomm).inv_right.eq
    calc a * ((x : G) * (y : G)) * a⁻¹ * ((x : G) * (y : G))⁻¹
        = (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ := by group
      _ = (a * (x : G) * a⁻¹) *
            ((a * (y : G) * a⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) := by group
      _ = (a * (x : G) * a⁻¹) *
            ((x : G)⁻¹ * (a * (y : G) * a⁻¹ * (y : G)⁻¹)) := by rw [htx]
      _ = (a * (x : G) * a⁻¹ * (x : G)⁻¹) *
            (a * (y : G) * a⁻¹ * (y : G)⁻¹) := by group

private def y6bK (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) : Subgroup ↥(M3 c.s) :=
  (c.s.fr.F.subgroupOf (y6bE16 c.toCtx5)).comap (y6bTheta c hH hF hRT hP haP haF)

private lemma y6bK_mem_iff (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) (w : ↥(M3 c.s)) :
    w ∈ y6bK c hH hF hRT hP haP haF ↔
      ∃ f ∈ c.s.fr.F, a * (w : G) * a⁻¹ = f * (w : G) := by
  change w ∈ (c.s.fr.F.subgroupOf (y6bE16 c.toCtx5)).comap
      (y6bTheta c hH hF hRT hP haP haF) ↔
    ∃ f ∈ c.s.fr.F, a * (w : G) * a⁻¹ = f * (w : G)
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  change a * (w : G) * a⁻¹ * (w : G)⁻¹ ∈ c.s.fr.F ↔
    ∃ f ∈ c.s.fr.F, a * (w : G) * a⁻¹ = f * (w : G)
  constructor
  · intro h
    exact ⟨a * (w : G) * a⁻¹ * (w : G)⁻¹, h, by group⟩
  · rintro ⟨f, hf, hfw⟩
    have h : a * (w : G) * a⁻¹ * (w : G)⁻¹ = f := by rw [hfw]; group
    rwa [h]

private lemma y6b_F_le_K (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) :
    c.s.fr.F.subgroupOf (M3 c.s) ≤ y6bK c hH hF hRT hP haP haF := by
  intro f hf
  rw [y6bK_mem_iff]
  refine ⟨1, (c.s.fr.F).one_mem, ?_⟩
  have hfG : (f : G) ∈ c.s.fr.F := Subgroup.mem_subgroupOf.mp hf
  rw [haF (f : G) hfG]
  group

private lemma y6b_K_conj (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c.toCtx5) {P : Subgroup G}
    (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) (haW : a ∉ y6bW c.toCtx5)
    {n w : G} (hn : n ∈ normIn L c.s.fr.F) (hw : w ∈ M3 c.s)
    (hwK : ∃ f ∈ c.s.fr.F, a * w * a⁻¹ = f * w) :
    ∃ f ∈ c.s.fr.F, a * (n * w * n⁻¹) * a⁻¹ = f * (n * w * n⁻¹) := by
  obtain ⟨f, hf, hfw⟩ := hwK
  have hyW : a⁻¹ * (n * a * n⁻¹) ∈ y6bW c.toCtx5 :=
    y6b_equivar c.toCtx5 hH hF hRT h1 (hP.2.1 haP) haF haW n hn
  have hxM : n * w * n⁻¹ ∈ M3 c.s :=
    (Subgroup.mem_normalizer_iff.mp (y6e_NL_le_normalizer_M3 c.toCtx5 hH hn) w).mp hw
  have hnf : n * f * n⁻¹ ∈ c.s.fr.F :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hn).2 f).mp hf
  set y : G := a⁻¹ * (n * a * n⁻¹) with hydef
  have hyW' : y ∈ y6bW c.toCtx5 := by rw [hydef]; exact hyW
  have hna : a * y = n * a * n⁻¹ := by rw [hydef]; group
  have hkey : a * (y * (n * w * n⁻¹) * y⁻¹) * a⁻¹ =
      (n * f * n⁻¹) * (n * w * n⁻¹) := by
    have h1' : a * (y * (n * w * n⁻¹) * y⁻¹) * a⁻¹ =
        (a * y) * (n * w * n⁻¹) * (a * y)⁻¹ := by group
    rw [h1', hna]
    calc (n * a * n⁻¹) * (n * w * n⁻¹) * (n * a * n⁻¹)⁻¹
        = n * (a * w * a⁻¹) * n⁻¹ := by group
      _ = n * (f * w) * n⁻¹ := by rw [hfw]
      _ = (n * f * n⁻¹) * (n * w * n⁻¹) := by group
  rcases y6b_W_conj_M3 c hH hF hRT hyW' hxM with hyx | hyx
  · exact ⟨n * f * n⁻¹, hnf, by rw [hyx] at hkey; exact hkey⟩
  · rw [hyx] at hkey
    refine ⟨(n * f * n⁻¹)⁻¹ * ((n * w * n⁻¹) ^ 2)⁻¹, ?_, ?_⟩
    · exact (c.s.fr.F).mul_mem ((c.s.fr.F).inv_mem hnf)
        ((c.s.fr.F).inv_mem (y6b_M3_sq_mem_F c hH hF (n * w * n⁻¹) hxM))
    · have h2 : a * (n * w * n⁻¹) * a⁻¹ =
          (n * w * n⁻¹)⁻¹ * (n * f * n⁻¹)⁻¹ := by
        have h3 : (a * (n * w * n⁻¹)⁻¹ * a⁻¹)⁻¹ =
            ((n * f * n⁻¹) * (n * w * n⁻¹))⁻¹ := congrArg Inv.inv hkey
        rw [show (a * (n * w * n⁻¹)⁻¹ * a⁻¹)⁻¹ = a * (n * w * n⁻¹) * a⁻¹ by group,
            show ((n * f * n⁻¹) * (n * w * n⁻¹))⁻¹ =
              (n * w * n⁻¹)⁻¹ * (n * f * n⁻¹)⁻¹ by group] at h3
        exact h3
      rw [h2]
      haveI := y6e_M3_comm c.toCtx5 hF
      have hfinv : (n * f * n⁻¹)⁻¹ ∈ M3 c.s :=
        (M3 c.s).inv_mem ((le_sup_right : c.s.fr.F ≤ M3 c.s) hnf)
      have hxinv : (n * w * n⁻¹)⁻¹ ∈ M3 c.s := (M3 c.s).inv_mem hxM
      rw [show (n * f * n⁻¹)⁻¹ * ((n * w * n⁻¹) ^ 2)⁻¹ * (n * w * n⁻¹) =
          (n * f * n⁻¹)⁻¹ * (((n * w * n⁻¹) ^ 2)⁻¹ * (n * w * n⁻¹)) by group]
      rw [show ((n * w * n⁻¹) ^ 2)⁻¹ * (n * w * n⁻¹) = (n * w * n⁻¹)⁻¹ by
        rw [pow_two, mul_inv_rev]; group]
      exact (Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hfinv hxinv).symm

private lemma y6bK_index_le_two (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) :
    (y6bK c hH hF hRT hP haP haF).index ≤ 2 := by
  let H : Subgroup ↥(y6bE16 c.toCtx5) := c.s.fr.F.subgroupOf (y6bE16 c.toCtx5)
  have hcardH : Nat.card ↥H = 8 := by
    change Nat.card ↥(c.s.fr.F.subgroupOf (y6bE16 c.toCtx5)) = 8
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y6b_F_le_E16 c.toCtx5)).toEquiv]
    simpa using (y54_F_isE3 hH).2
  have hcardE16 : Nat.card ↥(y6bE16 c.toCtx5) = 16 := y6b_card_E16 c.toCtx5 hH hRT
  have hindexH : H.index = 2 := by
    have h := Subgroup.index_mul_card (H := H)
    rw [hcardH, hcardE16] at h
    omega
  have hK : (y6bK c hH hF hRT hP haP haF).index =
      H.relIndex (y6bTheta c hH hF hRT hP haP haF).range := by
    change (H.comap (y6bTheta c hH hF hRT hP haP haF)).index = _
    exact Subgroup.index_comap (H := H) (f := y6bTheta c hH hF hRT hP haP haF)
  rw [hK]
  calc H.relIndex (y6bTheta c hH hF hRT hP haP haF).range
      ≤ H.relIndex (⊤ : Subgroup ↥(y6bE16 c.toCtx5)) :=
        Subgroup.relIndex_le_of_le_right le_top (by
          rw [Subgroup.relIndex_top_right (H := H), hindexH]
          norm_num)
    _ = 2 := by rw [Subgroup.relIndex_top_right (H := H), hindexH]

private lemma y6bK_card_ge (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) :
    32 ≤ Nat.card ↥(y6bK c hH hF hRT hP haP haF) := by
  have h := Subgroup.card_mul_index (H := y6bK c hH hF hRT hP haP haF)
  rw [y6e_card_M3 c.toCtx5 hH] at h
  have hidx := y6bK_index_le_two c hH hF hRT hP haP haF
  have hpos : 0 < (y6bK c hH hF hRT hP haP haF).index := by
    rcases Nat.eq_zero_or_pos (y6bK c hH hF hRT hP haP haF).index with h0 | h0
    · rw [h0, mul_zero] at h
      omega
    · exact h0
  have hidx_cases : (y6bK c hH hF hRT hP haP haF).index = 1 ∨
      (y6bK c hH hF hRT hP haP haF).index = 2 := by omega
  rcases hidx_cases with h1 | h2
  · rw [h1, mul_one] at h
    omega
  · rw [h2] at h
    omega

theorem y6b_a_conj_M3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c.toCtx5) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P)
    {a : G} (haP : a ∈ P) (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) (haW : a ∉ y6bW c.toCtx5) :
    ∀ w ∈ M3 c.s, ∃ f ∈ c.s.fr.F, a * w * a⁻¹ = f * w := by
  obtain ⟨u, huK0, huF0⟩ : ∃ u : ↥(M3 c.s), u ∈ y6bK c hH hF hRT hP haP haF ∧
      u ∉ c.s.fr.F.subgroupOf (M3 c.s) := by
    refine Set.not_subset.mp ?_
    intro hle
    have hle' := Subgroup.card_le_of_le hle
    have hFcard : Nat.card ↥(c.s.fr.F.subgroupOf (M3 c.s)) = 8 := by
      have e : ↥(c.s.fr.F.subgroupOf (M3 c.s)) ≃ ↥(c.s.fr.F) :=
        (Subgroup.subgroupOfEquivOfLe (le_sup_right : c.s.fr.F ≤ M3 c.s)).toEquiv
      rw [Nat.card_congr e]
      simpa using (y54_F_isE3 hH).2
    rw [hFcard] at hle'
    have hKcard := y6bK_card_ge c hH hF hRT hP haP haF
    omega
  have huK : ∃ f ∈ c.s.fr.F, a * (u : G) * a⁻¹ = f * (u : G) :=
    (y6bK_mem_iff c hH hF hRT hP haP haF u).mp huK0
  have huF : (u : G) ∉ c.s.fr.F := fun h => huF0 (Subgroup.mem_subgroupOf.mpr h)
  intro w hw
  by_cases hw2 : w ^ 2 = 1
  · have hwF : w ∈ c.s.fr.F := y6b_M3_sqone c hH hF w hw hw2
    refine ⟨1, (c.s.fr.F).one_mem, ?_⟩
    rw [haF w hwF]
    group
  · have hw2mem : w ^ 2 ∈ c.s.fr.F := y6b_M3_sq_mem_F c hH hF w hw
    have hu2mem : (u : G) ^ 2 ∈ c.s.fr.F := y6b_M3_sq_mem_F c hH hF (u : G) u.2
    have hu2ne : (u : G) ^ 2 ≠ 1 := fun h =>
      huF (y6b_M3_sqone c hH hF (u : G) u.2 h)
    obtain ⟨n, hn, hconj⟩ := y54_trans1 hH ((u : G) ^ 2) hu2mem (w ^ 2) hw2mem hu2ne hw2
    have hnun : n * (u : G) * n⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp (y6e_NL_le_normalizer_M3 c.toCtx5 hH hn)
        (u : G)).mp u.2
    set v : ↥(M3 c.s) := ⟨n * (u : G) * n⁻¹, hnun⟩ with hvdef
    have hstep := y6b_K_conj c hH hF hRT h1 hP haP haF haW hn u.2 huK
    have hvK : v ∈ y6bK c hH hF hRT hP haP haF :=
      (y6bK_mem_iff c hH hF hRT hP haP haF v).mpr (by
        show ∃ f ∈ c.s.fr.F, a * (n * (u : G) * n⁻¹) * a⁻¹ = f * (n * (u : G) * n⁻¹)
        exact hstep)
    have hv2 : (v : G) ^ 2 = w ^ 2 := by
      rw [hvdef]
      rw [show (n * (u : G) * n⁻¹) ^ 2 = n * (u : G) ^ 2 * n⁻¹ by
        rw [pow_two, pow_two]; group, hconj]
    have hxM : w * (v : G)⁻¹ ∈ M3 c.s :=
      (M3 c.s).mul_mem hw ((M3 c.s).inv_mem v.2)
    have hx2 : (w * (v : G)⁻¹) ^ 2 = 1 := by
      haveI := y6e_M3_comm c.toCtx5 hF
      have hc : Commute w ((v : G)⁻¹) :=
        Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hw ((M3 c.s).inv_mem v.2)
      rw [hc.mul_pow, inv_pow, hv2]
      group
    have hxF : w * (v : G)⁻¹ ∈ c.s.fr.F :=
      y6b_M3_sqone c hH hF (w * (v : G)⁻¹) hxM hx2
    have hxvK : (⟨w * (v : G)⁻¹, hxM⟩ : ↥(M3 c.s)) ∈ y6bK c hH hF hRT hP haP haF :=
      y6b_F_le_K c hH hF hRT hP haP haF (Subgroup.mem_subgroupOf.mpr hxF)
    have hwK : (⟨w, hw⟩ : ↥(M3 c.s)) ∈ y6bK c hH hF hRT hP haP haF := by
      have hweq : (⟨w, hw⟩ : ↥(M3 c.s)) = (⟨w * (v : G)⁻¹, hxM⟩ : ↥(M3 c.s)) * v := by
        apply Subtype.ext
        show w = (w * (v : G)⁻¹) * (v : G)
        group
      rw [hweq]
      exact (y6bK c hH hF hRT hP haP haF).mul_mem hxvK hvK
    obtain ⟨f, hf, hfw⟩ := (y6bK_mem_iff c hH hF hRT hP haP haF ⟨w, hw⟩).mp hwK
    exact ⟨f, hf, hfw⟩

end CFSG.OddStandard.HigherRank.YamadaG23
