module

public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ComponentClassification CFSG.GH74.GLS.Stage2.Local CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped MatrixGroups

section Sl2Three

private theorem q3_mul : ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

private theorem q3_conj : ∀ g a : SL(2, ZMod 3), a ^ 4 = 1 → (g * a * g⁻¹) ^ 4 = 1 := by
  decide +kernel

private theorem q3_comm : ∀ a b : SL(2, ZMod 3), ((a * b)⁻¹ * (b * a)) ^ 4 = 1 := by
  decide +kernel

private def q3 : Subgroup SL(2, ZMod 3) where
  carrier := {g | g ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := fun {a b} ha hb => q3_mul a b ha hb
  inv_mem' := fun {a} ha => by
    have h : a ^ 4 = 1 := ha
    show a⁻¹ ^ 4 = 1
    rw [inv_pow, h, inv_one]

private instance q3_normal : q3.Normal := ⟨fun a ha g => q3_conj g a ha⟩

theorem isSolvable_sl2_zmod_three : Group.IsSolvable SL(2, ZMod 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 q3 := fun x => ⟨2, by
    apply Subtype.ext
    have h : (x : SL(2, ZMod 3)) ^ 4 = 1 := x.2
    simpa [Subgroup.coe_pow] using h⟩
  have := hp.isNilpotent
  have : Group.IsSolvable q3 := inferInstance
  have : IsMulCommutative (SL(2, ZMod 3) ⧸ q3) := ⟨⟨fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact q3_comm x y⟩⟩
  exact Group.isSolvable_of_subgroup_quotient q3

theorem isSolvable_of_hasSL2Model_three {Q : Type} [Group Q]
    (h : HasSL2Model Q (fun r => r = 3)) : Group.IsSolvable Q := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let Φ : Q ≃* SL(2, ZMod 3) :=
    (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).trans (slMapEquiv φ)
  have := isSolvable_sl2_zmod_three
  exact Group.isSolvable_of_surjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective

end Sl2Three
theorem eq_or_eq_of_two_components {X : Type} [Group X] [Finite X]
    {L₁ L₂ : Subgroup (TwoThin.barQ X)}
    (hL : ∀ J : Subgroup (TwoThin.barQ X), IsComponent J → J = L₁ ∨ J = L₂)
    {A B K : Subgroup X} (hA : TwoComponents.IsTwoComponent A) (hB : TwoComponents.IsTwoComponent B)
    (hK : TwoComponents.IsTwoComponent K) (hAB : A ≠ B) : K = A ∨ K = B := by
  have himg : ∀ P Q : Subgroup X, TwoComponents.IsTwoComponent P → TwoComponents.IsTwoComponent Q →
      P.map (TwoThin.barMk X) = Q.map (TwoThin.barMk X) → P = Q := fun P Q hP hQ h =>
    OddKernelTwoComponents.lift_unique (TwoThin.barMk X) TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk P Q hP hQ h
  have hA' := TwoThin.isComponent_map_barMk hA
  have hB' := TwoThin.isComponent_map_barMk hB
  have hK' := TwoThin.isComponent_map_barMk hK
  by_contra hcon
  push Not at hcon
  have h1 : K.map (TwoThin.barMk X) ≠ A.map (TwoThin.barMk X) := fun h => hcon.1 (himg K A hK hA h)
  have h2 : K.map (TwoThin.barMk X) ≠ B.map (TwoThin.barMk X) := fun h => hcon.2 (himg K B hK hB h)
  have h3 : A.map (TwoThin.barMk X) ≠ B.map (TwoThin.barMk X) := fun h => hAB (himg A B hA hB h)
  rcases hL _ hK' with e | e <;> rcases hL _ hA' with a | a <;> rcases hL _ hB' with b | b <;>
    first
    | exact h1 (e.trans a.symm)
    | exact h2 (e.trans b.symm)
    | exact h3 (a.trans b.symm)


section Comps

theorem exists_mul_of_mem_sup_of_commute' {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := h₂
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← this]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv y _ h₁ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a⁻¹ * b = b * a⁻¹ := this
        calc b⁻¹ * a⁻¹ = b⁻¹ * (a⁻¹ * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

theorem le_normalizer_of_commute {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set Y) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : b * x * b⁻¹ = x := by rw [← h x hx b hb]; group
    rw [this]; exact hx
  · intro hx
    have hc : (b * x * b⁻¹) * b⁻¹ = b⁻¹ * (b * x * b⁻¹) := h _ hx b⁻¹ (B.inv_mem hb)
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = ((b * x * b⁻¹) * b⁻¹) * b := by rw [hc]
        _ = b * x * b⁻¹ := by group
    rw [this]; exact hx

theorem le_of_perfect_of_solvable {Y : Type*} [Group Y] {A B J : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hB : Group.IsSolvable ↥B)
    (hJ : Group.IsPerfect ↥J) (hle : J ≤ A ⊔ B) : J ≤ A := by
  have hAM : A ≤ A ⊔ B := le_sup_left
  have hBM : B ≤ A ⊔ B := le_sup_right
  have hN : (A.subgroupOf (A ⊔ B)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAM]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hcomm)
  let f : ↥B →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion hBM)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup_of_commute' hcomm x.2
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hBM ⟨b, hb⟩) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (b⁻¹ * (x : Y)) ∈ A
    rw [hx]
    have : b⁻¹ * (a * b) = a := by
      have h1 : a * b⁻¹ = b⁻¹ * a := hcomm a ha b⁻¹ (B.inv_mem hb)
      calc b⁻¹ * (a * b) = (b⁻¹ * a) * b := by group
        _ = (a * b⁻¹) * b := by rw [h1]
        _ = a := by group
    rw [this]; exact ha
  have hsol : Group.IsSolvable (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective hf
  let g : ↥J →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion hle)
  have hr : Group.IsPerfect g.range := Group.IsPerfect.range g
  have htriv : g.range = ⊥ := by
    by_contra hne
    have : Nontrivial g.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable g.range inferInstance
  intro j hj
  have h1 : g ⟨j, hj⟩ = 1 := by
    have hmem : g ⟨j, hj⟩ ∈ g.range := ⟨_, rfl⟩
    rw [htriv] at hmem
    exact hmem
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  exact Subgroup.mem_subgroupOf.1 h2

end Comps


section G2

variable {G : Type} [Group G] [Finite G]

theorem components_of_g2Shape {z : G} {S : Subgroup G} {r₁ r₂ : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (h : G2Shape z S r₁ r₂ L₁ L₂) :
    ∀ J : Subgroup (CentralizerBar z), IsComponent J → J = L₁ ∨ J = L₂ := by
  obtain ⟨ho₁, ho₂, hg₁, hcp, hs₁, hs₂, -, h3, h4, -, -, -⟩ := h
  obtain ⟨hsup, hcomm, -⟩ := hcp
  have hq₁ := (sl2_model_facts ho₁ (by omega) hs₁).1
  have hL₁le : L₁ ≤ LBar z := hsup ▸ le_sup_left
  have hL₂le : L₂ ≤ LBar z := hsup ▸ le_sup_right
  have hsub : ∀ L : Subgroup (CentralizerBar z), L ≤ LBar z → (L.subgroupOf (LBar z)).Normal →
      L.IsSubnormal := fun L hL hN =>
    Subgroup.IsSubnormal.step L (LBar z) hL (Subgroup.Normal.isSubnormal (LBar_normal z)) hN
  have hN₁ : (L₁.subgroupOf (LBar z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₁le, ← hsup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hcomm)
  have hN₂ : (L₂.subgroupOf (LBar z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hL₂le, ← hsup]
    exact sup_le (le_normalizer_of_commute (fun b hb a ha => (hcomm a ha b hb).symm)) Subgroup.le_normalizer
  have hc₁ : IsComponent L₁ := ⟨hq₁, hsub L₁ hL₁le hN₁⟩
  intro J hJ
  have h1 : J ≤ layer (CentralizerBar z) := le_sSup hJ
  have h2 : layer (CentralizerBar z) ≤ generalizedFitting (CentralizerBar z) := le_sup_right
  rcases Nat.lt_or_ge 3 r₂ with hgt | hle
  · have hJle : J ≤ L₁ ⊔ L₂ := by
      rw [hsup]
      exact (h1.trans h2).trans (h4 hgt).2.le
    have hq₂ := (sl2_model_facts ho₂ (by omega) hs₂).1
    have hc₂ : IsComponent L₂ := ⟨hq₂, hsub L₂ hL₂le hN₂⟩
    exact eq_or_eq_of_isComponent_le_sup hJ hc₁ hc₂ hJle
  · have hr₂ : r₂ = 3 := by
      obtain ⟨F, hF, hFin, hq, -⟩ := hs₂
      have : 1 < Nat.card F := Finite.one_lt_card
      have hq' : r₂ = Nat.card F := hq.symm
      obtain ⟨k, hk⟩ := ho₂
      omega
    subst hr₂
    have hJle : J ≤ L₁ ⊔ L₂ := by
      rw [hsup]
      refine (h1.trans h2).trans ?_
      rw [(h3 rfl).2]
      exact Subgroup.map_subtype_le _
    have hsol := isSolvable_of_hasSL2Model_three hs₂
    have hJL₁ : J ≤ L₁ := le_of_perfect_of_solvable hcomm hsol hJ.1.1 hJle
    left
    rcases eq_or_eq_of_isComponent_le_sup hJ hc₁ hc₁ (by rw [sup_idem]; exact hJL₁) with e | e <;> exact e

theorem noFAut_of_components {z : G} {S K₁ K₂ : Subgroup G} (h4 : Std4 G z S K₁ K₂)
    {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hL : ∀ J : Subgroup (CentralizerBar z), IsComponent J → J = L₁ ∨ J = L₂)
    (hc6 : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K) :
    ∀ s ∈ S, ∀ K : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K = 1 →
      InducesFAut s K → s ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  intro s hs K hK _ hf
  have hr1 : IsRigidRankOneComp z K₁ := by
    have : K₁ ∈ {K | IsRigidRankOneComp z K} := by rw [h4.comps]; simp
    exact this
  have hr2 : IsRigidRankOneComp z K₂ := by
    have : K₂ ∈ {K | IsRigidRankOneComp z K} := by rw [h4.comps]; simp
    exact this
  have hA : IsPCompIn 2 (centralizer ({z} : Set G)) K₁ := hr1.1.1.2.2
  have hB : IsPCompIn 2 (centralizer ({z} : Set G)) K₂ := hr2.1.1.2.2
  obtain ⟨hKC, hK2⟩ := TwoThin.isPCompIn_two_iff.mp hK
  obtain ⟨hAC, hA2⟩ := TwoThin.isPCompIn_two_iff.mp hA
  obtain ⟨hBC, hB2⟩ := TwoThin.isPCompIn_two_iff.mp hB
  have hAB : K₁.subgroupOf (centralizer ({z} : Set G)) ≠ K₂.subgroupOf (centralizer ({z} : Set G)) := by
    intro h
    have := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hAC, inf_eq_left.mpr hBC] at this
    exact h4.ne this
  rcases eq_or_eq_of_two_components hL hA2 hB2 hK2 hAB with h | h
  · have := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hKC, inf_eq_left.mpr hAC] at this
    subst this
    exact hc6 K hr1 s hs hf
  · have := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hKC, inf_eq_left.mpr hBC] at this
    subst this
    exact hc6 K hr2 s hs hf

theorem noFAut_thm : NoFAutBridge := by
  intro G _ _ z S k hcen hdata hk K₁ K₂ h4 hc6
  rcases hk with rfl | rfl | ⟨ε, rfl⟩
  · cases hdata with
    | g2 hg =>
      obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
      exact noFAut_of_components h4 (components_of_g2Shape hsh) hc6
  · cases hdata with
    | psp4 hp =>
      obtain ⟨q, L₁, L₂, hq⟩ := hp
      refine noFAut_of_components (L₁ := L₁) (L₂ := L₂) h4 (fun J hJ => ?_) hc6
      have hmem : J ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := hJ
      rw [hq.pair.comps] at hmem
      simpa using hmem
  · cases hdata with
    | l4 _ hp =>
      obtain ⟨q, L₁, L₂, hq⟩ := hp
      refine noFAut_of_components (L₁ := L₁) (L₂ := L₂) h4 (fun J hJ => ?_) hc6
      have hmem : J ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := hJ
      rw [hq.pair.comps] at hmem
      simpa using hmem

end G2


section R1

theorem eq_of_unique_component {X : Type} [Group X] [Finite X] {L : Subgroup (TwoThin.barQ X)}
    (hL : ∀ J : Subgroup (TwoThin.barQ X), IsComponent J → J = L)
    {A K : Subgroup X} (hA : TwoComponents.IsTwoComponent A) (hK : TwoComponents.IsTwoComponent K) :
    K = A :=
  OddKernelTwoComponents.lift_unique (TwoThin.barMk X) TwoThin.barMk_surjective
    TwoThin.odd_card_ker_barMk K A hK hA
    ((hL _ (TwoThin.isComponent_map_barMk hK)).trans (hL _ (TwoThin.isComponent_map_barMk hA)).symm)

theorem le_of_perfect_of_solvable_quotient {Y : Type*} [Group Y] {M N J : Subgroup Y}
    [(N.subgroupOf M).Normal] (hsol : Group.IsSolvable (↥M ⧸ N.subgroupOf M))
    (hJ : Group.IsPerfect ↥J) (hJM : J ≤ M) : J ≤ N := by
  let g : ↥J →* ↥M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hJM)
  have hr : Group.IsPerfect g.range := Group.IsPerfect.range g
  have htriv : g.range = ⊥ := by
    by_contra hne
    have : Nontrivial g.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable g.range inferInstance
  intro j hj
  have h1 : g ⟨j, hj⟩ = 1 := by
    have hmem : g ⟨j, hj⟩ ∈ g.range := ⟨_, rfl⟩
    rw [htriv] at hmem
    exact hmem
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

theorem le_of_perfect_of_solvable_quotient_top {Y : Type*} [Group Y] {N J : Subgroup Y} [N.Normal]
    (hsol : Group.IsSolvable (Y ⧸ N)) (hJ : Group.IsPerfect ↥J) : J ≤ N := by
  let g : ↥J →* Y ⧸ N := (QuotientGroup.mk' N).comp J.subtype
  have hr : Group.IsPerfect g.range := Group.IsPerfect.range g
  have htriv : g.range = ⊥ := by
    by_contra hne
    have : Nontrivial g.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable g.range inferInstance
  intro j hj
  have h1 : g ⟨j, hj⟩ = 1 := by
    have hmem : g ⟨j, hj⟩ ∈ g.range := ⟨_, rfl⟩
    rw [htriv] at hmem
    exact hmem
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem odd_card_quotient_oPrimeResidual (Y : Type*) [Group Y] [Finite Y] :
    Odd (Nat.card (Y ⧸ oPrimeResidual 2 Y)) := by
  have := Stage1.Thm6.Prod.oPrimeResidual_normal 2 Y
  by_contra hne
  have h2 : 2 ∣ Nat.card (Y ⧸ oPrimeResidual 2 Y) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hg : g ^ m ∈ oPrimeResidual 2 Y := by
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have h1 : (QuotientGroup.mk g : Y ⧸ oPrimeResidual 2 Y) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hg
  have h3 : orderOf (QuotientGroup.mk g : Y ⧸ oPrimeResidual 2 Y) ∣ m := orderOf_dvd_of_pow_eq_one h1
  rw [ha] at h3
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)


theorem isSolvable_of_card_two (Q : Type*) [Group Q] (h : Nat.card Q = 2) : Group.IsSolvable Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic Q := isCyclic_of_prime_card h
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hg b
  rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm]

theorem exists_unique_component_of_sl2Three {Y : Type} [Group Y] [Finite Y]
    (h : HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 Y) 3) :
    ∃ A : Subgroup Y, ∀ J : Subgroup Y, IsComponent J → J = A := by
  obtain ⟨F₁, F₂, i₁, i₂, f₁, f₂, ho₁, ho₂, hle, hF₂, h5, -, Kp, hKpC, hidx, hcp⟩ := h
  obtain ⟨A, B, hsup, hcomm, hcard, ⟨eA⟩, ⟨eB⟩⟩ := hcp
  have hC₁n : (oPrimeResidual 2 Y).Normal := Stage1.Thm6.Prod.oPrimeResidual_normal 2 Y
  have hsA : HasSL2Model ↥A (fun r => r = Nat.card F₁) := ⟨F₁, i₁, f₁, rfl, ⟨eA⟩⟩
  have hsB : HasSL2Model ↥B (fun r => r = 3) := ⟨F₂, i₂, f₂, hF₂, ⟨eB⟩⟩
  have hqA := (sl2_model_facts ho₁ (by omega) hsA).1
  have hAK : A ≤ Kp := hsup ▸ le_sup_left
  have hKn : (Kp.subgroupOf (oPrimeResidual 2 Y)).Normal := Subgroup.normal_of_index_eq_two hidx
  have hsub : Kp.IsSubnormal :=
    Subgroup.IsSubnormal.step Kp (oPrimeResidual 2 Y) hKpC (Subgroup.Normal.isSubnormal hC₁n) hKn
  have hNA : (A.subgroupOf Kp).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAK, ← hsup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hcomm)
  have hcA : IsComponent A := ⟨hqA, Subgroup.IsSubnormal.step A Kp hAK hsub hNA⟩
  refine ⟨A, fun J hJ => ?_⟩
  have hJperf : Group.IsPerfect ↥J := hJ.1.1
  have hJC : J ≤ oPrimeResidual 2 Y := by
    have hsolY : Group.IsSolvable (Y ⧸ oPrimeResidual 2 Y) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_quotient_oPrimeResidual Y)
    exact le_of_perfect_of_solvable_quotient_top hsolY hJperf
  have hJK : J ≤ Kp := by
    have hsol2 : Group.IsSolvable (↥(oPrimeResidual 2 Y) ⧸ Kp.subgroupOf (oPrimeResidual 2 Y)) :=
      isSolvable_of_card_two _ hidx
    exact le_of_perfect_of_solvable_quotient hsol2 hJperf hJC
  have hJA : J ≤ A := le_of_perfect_of_solvable hcomm (isSolvable_of_hasSL2Model_three hsB) hJperf
    (hsup ▸ hJK)
  rcases eq_or_eq_of_isComponent_le_sup hJ hcA hcA (by rw [sup_idem]; exact hJA) with e | e <;> exact e

theorem noFAutR1_thm : NoFAutBridgeR1 := by
  intro G _ _ z S k hcen hdata hk K₀ h6 hg hc6
  obtain ⟨q, -, -, -, -, -, -, -, hP⟩ := hg
  obtain ⟨A, hA⟩ := exists_unique_component_of_sl2Three (Y := CentralizerBar z) hP
  have hr0 : IsRigidRankOneComp z K₀ := by
    have : K₀ ∈ {K | IsRigidRankOneComp z K} := by rw [h6.comps]; rfl
    exact this
  have hK0 : IsPCompIn 2 (centralizer ({z} : Set G)) K₀ := hr0.1.1.2.2
  intro s hs K hK _ hf
  obtain ⟨hKC, hK2⟩ := TwoThin.isPCompIn_two_iff.mp hK
  obtain ⟨hAC, hA2⟩ := TwoThin.isPCompIn_two_iff.mp hK0
  have hKK := eq_of_unique_component (X := ↥(centralizer ({z} : Set G))) (L := A) hA hA2 hK2
  have h := Subgroup.subgroupOf_inj.mp hKK
  rw [inf_eq_left.mpr hKC, inf_eq_left.mpr hAC] at h
  subst h
  exact hc6 K hr0 s hs hf

end R1

end CFSG.GH74.GLS.Stage1.Main
