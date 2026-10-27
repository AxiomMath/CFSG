module

public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_le_of_isElemAbelian_of_isCyclic {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) (hc : IsCyclic E) : Nat.card E ≤ p := by
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hE.2 g g.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd hp.out.pos hexp

omit [Finite G] in
theorem not_isCyclic_of_isElemAbelian {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hc
  have h1 := card_le_of_isElemAbelian_of_isCyclic hE hc
  have h2 : p < p ^ 2 := by
    have := hp.out.one_lt
    nlinarith
  omega

omit [Finite G] in
theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite G] in
theorem pow_three_mem_of_mem_sup {E D : Subgroup G} (hE : ∀ e ∈ E, e ^ 3 = 1)
    (hED : E ≤ Subgroup.normalizer (D : Set G)) {x : G} (hx : x ∈ E ⊔ D) : x ^ 3 ∈ D := by
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D E hED,
    Set.mem_mul] at hx
  obtain ⟨d, hd, e, he, rfl⟩ := hx
  have hconj : ∀ y ∈ D, e * y * e⁻¹ ∈ D := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hED he) y).mp hy
  have hconj2 : ∀ y ∈ D, e⁻¹ * y * e ∈ D := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hED he)) y).mp hy
    simpa using this
  have he3 : e ^ 3 = 1 := hE e he
  have hkey : (d * e) ^ 3 = d * (e * d * e⁻¹) * (e * e * d * e⁻¹ * e⁻¹) * e ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [hkey, he3, mul_one]
  refine D.mul_mem (D.mul_mem hd (hconj d hd)) ?_
  have h1 := hconj _ (hconj d hd)
  simpa [mul_assoc] using h1

theorem card_le_three_mul_of_isCyclic {X Y : Subgroup G} (hX : IsCyclic X)
    (hcube : ∀ x ∈ X, x ^ 3 ∈ Y) : Nat.card X ≤ 3 * Nat.card (X ⊓ Y : Subgroup G) := by
  obtain ⟨⟨x, hxX⟩, hgen⟩ := hX.exists_generator
  have hXz : X = Subgroup.zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := hgen ⟨y, hy⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    · exact (Subgroup.zpowers_le).mpr hxX
  have hle : Subgroup.zpowers (x ^ 3) ≤ X ⊓ Y := by
    rw [Subgroup.zpowers_le]
    exact ⟨X.pow_mem hxX 3, hcube x hxX⟩
  have h1 : Nat.card (Subgroup.zpowers (x ^ 3)) ≤ Nat.card (X ⊓ Y : Subgroup G) :=
    Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have hXc : Nat.card X = orderOf x := by rw [hXz, Nat.card_zpowers]
  rw [hXc]
  have hpos : 0 < orderOf x := orderOf_pos x
  have hpow : orderOf (x ^ 3) = orderOf x / Nat.gcd (orderOf x) 3 := orderOf_pow' x (by norm_num)
  have hg : Nat.gcd (orderOf x) 3 ∣ 3 := Nat.gcd_dvd_right _ _
  have hg3 : Nat.gcd (orderOf x) 3 ≤ 3 := Nat.le_of_dvd (by norm_num) hg
  have hdiv : orderOf x = Nat.gcd (orderOf x) 3 * orderOf (x ^ 3) := by
    rw [hpow, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  calc orderOf x = Nat.gcd (orderOf x) 3 * orderOf (x ^ 3) := hdiv
    _ ≤ 3 * orderOf (x ^ 3) := Nat.mul_le_mul_right _ hg3
    _ ≤ 3 * Nat.card (X ⊓ Y : Subgroup G) := Nat.mul_le_mul_left _ h1

theorem arith_false {a x b : ℕ} (h : 81 * a = x * b) (hx : x ≤ 3 * a) (hb : b ≤ 9)
    (ha : 0 < a) : False := by
  have : x * b ≤ 3 * a * 9 := Nat.mul_le_mul hx hb
  omega

theorem arith_one {a x b : ℕ} (h : 81 * a = x * b) (hx : x ≤ 9) (hb : b ≤ 9) (ha : 0 < a) :
    a = 1 := by
  have : x * b ≤ 9 * 9 := Nat.mul_le_mul hx hb
  omega

theorem arith_nine {x b : ℕ} (h : 81 * 1 = x * b) (hx : x ≤ 9) (hb : b ≤ 9) :
    x = 9 ∧ b = 9 := by
  interval_cases x <;> omega

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_of_normal_mul'
    {M C B : Subgroup G} (hCM : C ≤ M)
    (hCn : M ≤ Subgroup.normalizer (C : Set G)) (hBM : B ≤ M)
    (hfac : ∀ m ∈ M, ∃ c ∈ C, ∃ b ∈ B, m = c * b) :
    ∃ W W₂ : Subgroup G, W ≤ M ∧ IsPGroup 3 W ∧ ¬ 3 ∣ (W.subgroupOf M).index ∧ W₂ ≤ B ∧
      W₂ ≤ W ∧ ¬ 3 ∣ (W₂.subgroupOf B).index ∧ ∀ w ∈ W, ∃ a ∈ W ⊓ C, ∃ b ∈ W₂, w = a * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₂⟩ : Nonempty (Sylow 3 B) := inferInstance
  obtain ⟨W₂, hW₂def⟩ : ∃ W₂ : Subgroup G, W₂ = (S₂ : Subgroup B).map B.subtype := ⟨_, rfl⟩
  have hW₂B : W₂ ≤ B := hW₂def ▸ Subgroup.map_subtype_le _
  have hW₂M : W₂ ≤ M := hW₂B.trans hBM
  have hW₂p : IsPGroup 3 W₂ := hW₂def ▸ S₂.isPGroup'.map B.subtype
  have hW₂sub : W₂.subgroupOf B = (S₂ : Subgroup B) := by
    rw [hW₂def]
    exact Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
  have hW₂idx : ¬ 3 ∣ (W₂.subgroupOf B).index := by
    rw [hW₂sub]
    exact S₂.not_dvd_index
  have hLM : C ⊔ W₂ ≤ M := sup_le hCM hW₂M
  have hCBM : C ⊔ B = M := by
    refine le_antisymm (sup_le hCM hBM) fun m hm => ?_
    obtain ⟨c, hc, b, hb, rfl⟩ := hfac m hm
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hb)
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hBM.trans hCn)
  rw [hCBM] at h1
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hW₂M.trans hCn)
  have h3 : (W₂.subgroupOf B).index * Nat.card W₂ = Nat.card B := by
    rw [← Subgroup.index_mul_card (W₂.subgroupOf B),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₂B).toEquiv]
  have hCW₂B : C ⊓ W₂ ≤ C ⊓ B := inf_le_inf_left C hW₂B
  have h4' : ((C ⊓ W₂).subgroupOf (C ⊓ B)).index * Nat.card (C ⊓ W₂ : Subgroup G) =
      Nat.card (C ⊓ B : Subgroup G) := by
    rw [← Subgroup.index_mul_card ((C ⊓ W₂).subgroupOf (C ⊓ B)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW₂B).toEquiv]
  have h5 : ((C ⊔ W₂).subgroupOf M).index * Nat.card (C ⊔ W₂ : Subgroup G) = Nat.card M := by
    rw [← Subgroup.index_mul_card ((C ⊔ W₂).subgroupOf M),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
  have hposL : 0 < Nat.card (C ⊔ W₂ : Subgroup G) * Nat.card (C ⊓ W₂ : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hkey : ((C ⊔ W₂).subgroupOf M).index * ((C ⊓ W₂).subgroupOf (C ⊓ B)).index *
      (Nat.card (C ⊔ W₂ : Subgroup G) * Nat.card (C ⊓ W₂ : Subgroup G)) =
      (W₂.subgroupOf B).index * (Nat.card (C ⊔ W₂ : Subgroup G) *
        Nat.card (C ⊓ W₂ : Subgroup G)) := by
    calc ((C ⊔ W₂).subgroupOf M).index * ((C ⊓ W₂).subgroupOf (C ⊓ B)).index *
          (Nat.card (C ⊔ W₂ : Subgroup G) * Nat.card (C ⊓ W₂ : Subgroup G))
        = (((C ⊔ W₂).subgroupOf M).index * Nat.card (C ⊔ W₂ : Subgroup G)) *
          (((C ⊓ W₂).subgroupOf (C ⊓ B)).index * Nat.card (C ⊓ W₂ : Subgroup G)) := by ring
      _ = Nat.card M * Nat.card (C ⊓ B : Subgroup G) := by rw [h5, h4']
      _ = Nat.card C * Nat.card B := h1
      _ = Nat.card C * ((W₂.subgroupOf B).index * Nat.card W₂) := by rw [h3]
      _ = (W₂.subgroupOf B).index * (Nat.card C * Nat.card W₂) := by ring
      _ = (W₂.subgroupOf B).index * (Nat.card (C ⊔ W₂ : Subgroup G) *
          Nat.card (C ⊓ W₂ : Subgroup G)) := by rw [← h2]
  have hidxeq := Nat.eq_of_mul_eq_mul_right hposL hkey
  have hLidx : ¬ 3 ∣ ((C ⊔ W₂).subgroupOf M).index := fun h =>
    hW₂idx (hidxeq ▸ Dvd.dvd.mul_right h _)
  have hW₂L : W₂ ≤ C ⊔ W₂ := le_sup_right
  have hpL : IsPGroup 3 (W₂.subgroupOf (C ⊔ W₂)) :=
    hW₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hW₂L).symm
  obtain ⟨S, hS⟩ := hpL.exists_le_sylow
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = (S : Subgroup (C ⊔ W₂ : Subgroup G)).map
      (C ⊔ W₂).subtype := ⟨_, rfl⟩
  have hWL : W ≤ C ⊔ W₂ := hWdef ▸ Subgroup.map_subtype_le _
  have hWM : W ≤ M := hWL.trans hLM
  have hW₂W : W₂ ≤ W := fun x hx => by
    rw [hWdef]
    exact ⟨⟨x, hW₂L hx⟩, hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hWp : IsPGroup 3 W := hWdef ▸ S.isPGroup'.map (C ⊔ W₂).subtype
  have hWsub : W.subgroupOf (C ⊔ W₂) = (S : Subgroup (C ⊔ W₂ : Subgroup G)) := by
    rw [hWdef]
    exact Subgroup.comap_map_eq_self_of_injective (C ⊔ W₂).subtype_injective _
  have hWidx : ¬ 3 ∣ (W.subgroupOf M).index := by
    have hrel := Subgroup.relIndex_mul_relIndex W (C ⊔ W₂) M hWL hLM
    intro h3'
    have h3'' : 3 ∣ W.relIndex (C ⊔ W₂) * (C ⊔ W₂).relIndex M := by rw [hrel]; exact h3'
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3'' with h | h
    · apply S.not_dvd_index
      have : W.relIndex (C ⊔ W₂) = (S : Subgroup (C ⊔ W₂ : Subgroup G)).index := by
        rw [Subgroup.relIndex, hWsub]
      rwa [this] at h
    · exact hLidx h
  refine ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hW₂idx, fun w hw => ?_⟩
  have hwL := hWL hw
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left C W₂ (hW₂M.trans hCn),
    Set.mem_mul] at hwL
  obtain ⟨c, hc, b, hb, rfl⟩ := hwL
  refine ⟨c, ⟨?_, hc⟩, b, hb, rfl⟩
  have := W.mul_mem hw (W.inv_mem (hW₂W hb))
  simpa using this

theorem exists_sylow_of_normal_mul {M C B : Subgroup G} (hCM : C ≤ M)
    (hCn : M ≤ Subgroup.normalizer (C : Set G)) (hBM : B ≤ M)
    (hfac : ∀ m ∈ M, ∃ c ∈ C, ∃ b ∈ B, m = c * b) :
    ∃ W W₂ : Subgroup G, W ≤ M ∧ IsPGroup 3 W ∧ ¬ 3 ∣ (W.subgroupOf M).index ∧ W₂ ≤ B ∧
      W₂ ≤ W ∧ ∀ w ∈ W, ∃ a ∈ W ⊓ C, ∃ b ∈ W₂, w = a * b := by
  obtain ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, -, hfac'⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_of_normal_mul' hCM hCn hBM hfac
  exact ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hfac'⟩

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.exists_elemAbelian_le_sylow_pow
    {M W : Subgroup G} {k : ℕ} (hWM : W ≤ M)
    (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hk : k ≤ Open.pRank 3 M) :
    ∃ E : Subgroup G, E ≤ W ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEM, hEel, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := k) hk
  have hEp : IsPGroup 3 (E.subgroupOf M) := by
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEc]
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  have hWp' : IsPGroup 3 (W.subgroupOf M) :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S' (hWp'.toSylow hWidx)
  have hgcoe : MulAut.conj g • (S' : Subgroup M) = W.subgroupOf M := by
    have := congrArg (fun S : Sylow 3 M => (S : Subgroup M)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
  refine ⟨E.map (MulAut.conj (g : G)).toMonoidHom, ?_,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxS : (⟨x, hEM hx⟩ : M) ∈ (S' : Subgroup M) := hS' (Subgroup.mem_subgroupOf.mpr hx)
    have hmem : MulAut.conj g • (⟨x, hEM hx⟩ : M) ∈ MulAut.conj g • (S' : Subgroup M) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hxS
    rw [hgcoe, Subgroup.mem_subgroupOf] at hmem
    simpa [MulAut.smul_def] using hmem
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hEc]

theorem exists_elemAbelian_le_sylow {M W : Subgroup G} (hWM : W ≤ M) (hWp : IsPGroup 3 W)
    (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (h4 : 4 ≤ Open.pRank 3 M) :
    ∃ E : Subgroup G, E ≤ W ∧ IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  obtain ⟨E, hEW, hEel, hEc⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_elemAbelian_le_sylow_pow hWM hWp hWidx h4
  exact ⟨E, hEW, hEel, by rw [hEc]; norm_num⟩

theorem eq_of_elemAbelian_of_mul {C B W W₂ E : Subgroup G}
    (hWC : W ≤ Subgroup.normalizer (C : Set G)) (hWp : IsPGroup 3 W) (hW₂B : W₂ ≤ B)
    (hW₂W : W₂ ≤ W) (hWfac : ∀ w ∈ W, ∃ a ∈ W ⊓ C, ∃ b ∈ W₂, w = a * b)
    (hC9 : ∀ X : Subgroup G, X ≤ C → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9)
    (hB9 : ∀ X : Subgroup G, X ≤ B → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9)
    (hEW : E ≤ W) (hEel : IsElemAbelian 3 E) (hEc : Nat.card E = 81) :
    Nat.card (W ⊓ C : Subgroup G) = 9 ∧ Nat.card W₂ = 9 ∧ (W ⊓ C) ⊓ W₂ = ⊥ ∧ E = W ∧
      (W ⊓ C) ⊔ W₂ = W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W₁, hW₁def⟩ : ∃ W₁ : Subgroup G, W₁ = W ⊓ C := ⟨_, rfl⟩
  rw [← hW₁def] at hWfac ⊢
  have hW₁W : W₁ ≤ W := hW₁def ▸ inf_le_left
  have hW₁C : W₁ ≤ C := hW₁def ▸ inf_le_right
  have hW₂p : IsPGroup 3 W₂ := hWp.to_le hW₂W
  have hWW₁ : W ≤ Subgroup.normalizer (W₁ : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hwC := hWC hw
    rw [hW₁def]
    constructor
    · rintro ⟨hxW, hxC⟩
      exact ⟨W.mul_mem (W.mul_mem hw hxW) (W.inv_mem hw),
        (Subgroup.mem_normalizer_iff.mp hwC x).mp hxC⟩
    · rintro ⟨hxW, hxC⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hwC x).mpr hxC⟩
      have := W.mul_mem (W.mul_mem (W.inv_mem hw) hxW) hw
      simpa [mul_assoc] using this
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G, X = W₂ ⊓ (E ⊔ W₁) := ⟨_, rfl⟩
  have hXW₂ : X ≤ W₂ := hXdef ▸ inf_le_left
  have hXEW : X ≤ E ⊔ W₁ := hXdef ▸ inf_le_right
  have hEW₁ : E ≤ Subgroup.normalizer (W₁ : Set G) := hEW.trans hWW₁
  have hXW₁ : X ≤ Subgroup.normalizer (W₁ : Set G) := (hXW₂.trans hW₂W).trans hWW₁
  have hsupeq : W₁ ⊔ E = W₁ ⊔ X := by
    apply le_antisymm
    · refine sup_le le_sup_left fun e he => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := hWfac e (hEW he)
      have hbX : b ∈ X := by
        rw [hXdef]
        refine ⟨hb, ?_⟩
        have : a⁻¹ * (a * b) ∈ E ⊔ W₁ :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_right (W₁.inv_mem ha)) (Subgroup.mem_sup_left he)
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbX)
    · refine sup_le le_sup_left fun x hx => ?_
      have hx2 := hXEW hx
      rw [sup_comm] at hx2
      exact hx2
  have hc1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hEW₁
  have hc2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hXW₁
  rw [hsupeq] at hc1
  have hposW₁ : 0 < Nat.card W₁ := Nat.card_pos
  have hrel : Nat.card E * Nat.card (W₁ ⊓ X : Subgroup G) =
      Nat.card X * Nat.card (W₁ ⊓ E : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left hposW₁
    calc Nat.card W₁ * (Nat.card E * Nat.card (W₁ ⊓ X : Subgroup G))
        = (Nat.card W₁ * Nat.card E) * Nat.card (W₁ ⊓ X : Subgroup G) := by ring
      _ = (Nat.card (W₁ ⊔ X : Subgroup G) * Nat.card (W₁ ⊓ E : Subgroup G)) *
          Nat.card (W₁ ⊓ X : Subgroup G) := by rw [hc1]
      _ = (Nat.card (W₁ ⊔ X : Subgroup G) * Nat.card (W₁ ⊓ X : Subgroup G)) *
          Nat.card (W₁ ⊓ E : Subgroup G) := by ring
      _ = (Nat.card W₁ * Nat.card X) * Nat.card (W₁ ⊓ E : Subgroup G) := by rw [hc2]
      _ = Nat.card W₁ * (Nat.card X * Nat.card (W₁ ⊓ E : Subgroup G)) := by ring
  rw [hEc] at hrel
  have hW₁Eel : IsElemAbelian 3 (W₁ ⊓ E : Subgroup G) := isElemAbelian_of_le hEel inf_le_right
  have hW₁Ep : IsPGroup 3 (W₁ ⊓ E : Subgroup G) := hWp.to_le (inf_le_left.trans hW₁W)
  have hb1 : Nat.card (W₁ ⊓ E : Subgroup G) ≤ 9 := by
    by_cases hcyc : IsCyclic (W₁ ⊓ E : Subgroup G)
    · have := card_le_of_isElemAbelian_of_isCyclic hW₁Eel hcyc
      omega
    · exact hC9 _ (inf_le_left.trans hW₁C) hW₁Ep hcyc
  have hXp : IsPGroup 3 X := hW₂p.to_le hXW₂
  have hposWX : 0 < Nat.card (W₁ ⊓ X : Subgroup G) := Nat.card_pos
  have hXnc : ¬ IsCyclic X := by
    intro hcyc
    have hcube : ∀ x ∈ X, x ^ 3 ∈ W₁ := fun x hx =>
      pow_three_mem_of_mem_sup hEel.2 hEW₁ (hXEW hx)
    have hle := card_le_three_mul_of_isCyclic hcyc hcube
    rw [inf_comm] at hle
    exact arith_false hrel hle hb1 hposWX
  have hX9 : Nat.card X ≤ 9 := hB9 X (hXW₂.trans hW₂B) hXp hXnc
  have hWX1 : Nat.card (W₁ ⊓ X : Subgroup G) = 1 := arith_one hrel hX9 hb1 hposWX
  rw [hWX1] at hrel
  obtain ⟨hXc9, hWE9⟩ := arith_nine hrel hX9 hb1
  have hW₁nc : ¬ IsCyclic W₁ := by
    intro hcyc
    have : IsCyclic (W₁ ⊓ E : Subgroup G) := Subgroup.isCyclic_of_le inf_le_left
    have := card_le_of_isElemAbelian_of_isCyclic hW₁Eel this
    omega
  have hW₁9 : Nat.card W₁ ≤ 9 := hC9 W₁ hW₁C (hWp.to_le hW₁W) hW₁nc
  have hW₁c : Nat.card W₁ = 9 :=
    le_antisymm hW₁9 (hWE9 ▸ Subgroup.card_le_of_le inf_le_left)
  have hW₂nc : ¬ IsCyclic W₂ := by
    intro hcyc
    exact hXnc (Subgroup.isCyclic_of_le hXW₂)
  have hW₂9 : Nat.card W₂ ≤ 9 := hB9 W₂ hW₂B hW₂p hW₂nc
  have hXeq : X = W₂ := Subgroup.eq_of_le_of_card_ge hXW₂ (by omega)
  have hW₂c : Nat.card W₂ = 9 := by rw [← hXeq]; exact hXc9
  have hW₁₂ : W₁ ⊓ W₂ = ⊥ := by
    rw [← hXeq]
    exact Subgroup.eq_bot_of_card_eq _ hWX1
  have hWeq : W₁ ⊔ W₂ = W := by
    refine le_antisymm (sup_le hW₁W hW₂W) fun w hw => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hcW := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hW₂W.trans hWW₁)
  rw [hW₁₂, Subgroup.card_bot, mul_one, hW₁c, hW₂c] at hcW
  have hWc : Nat.card W = 81 := by rw [← hWeq]; exact hcW
  exact ⟨hW₁c, hW₂c, hW₁₂, Subgroup.eq_of_le_of_card_ge hEW (by rw [hWc, hEc]), hWeq⟩

theorem exists_elemAbelian_of_normal_mul {M C B : Subgroup G} (hCM : C ≤ M)
    (hCn : M ≤ Subgroup.normalizer (C : Set G)) (hBM : B ≤ M)
    (hfac : ∀ m ∈ M, ∃ c ∈ C, ∃ b ∈ B, m = c * b)
    (hC9 : ∀ X : Subgroup G, X ≤ C → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9)
    (hB9 : ∀ X : Subgroup G, X ≤ B → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9)
    (h4 : 4 ≤ Open.pRank 3 M) :
    ∃ W₁ W₂ : Subgroup G, W₁ ≤ C ∧ W₂ ≤ B ∧ Nat.card W₁ = 9 ∧ Nat.card W₂ = 9 ∧
      W₁ ⊓ W₂ = ⊥ ∧ IsElemAbelian 3 (W₁ ⊔ W₂ : Subgroup G) ∧
      Nat.card (W₁ ⊔ W₂ : Subgroup G) = 81 ∧ W₁ ⊔ W₂ ≤ M ∧
      ¬ 3 ∣ ((W₁ ⊔ W₂).subgroupOf M).index ∧ W₁ = (W₁ ⊔ W₂) ⊓ C := by
  obtain ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hWfac⟩ :=
    exists_sylow_of_normal_mul hCM hCn hBM hfac
  obtain ⟨E, hEW, hEel, hEc⟩ := exists_elemAbelian_le_sylow hWM hWp hWidx h4
  obtain ⟨hW₁c, hW₂c, hW₁₂, hEeq, hWeq⟩ :=
    eq_of_elemAbelian_of_mul (hWM.trans hCn) hWp hW₂B hW₂W hWfac hC9 hB9 hEW hEel hEc
  refine ⟨W ⊓ C, W₂, inf_le_right, hW₂B, hW₁c, hW₂c, hW₁₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWeq, ← hEeq]
    exact hEel
  · rw [hWeq, ← hEeq]
    exact hEc
  · rw [hWeq]
    exact hWM
  · rw [hWeq]
    exact hWidx
  · rw [hWeq]

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
