module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTwCore
public import CFSG.LieType.ChevTwo.OppositeFixedExcE6

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiag rootDiagUnit rootChar
  rootDiag_single rootChar_add rootChar_zero root_diagonal_conjugation end_ext_single)

variable {K : Type} [Field K]

@[expose] def semiMulSub {τ : Tag} (H D : Subgroup (ModGL τ K))
    (hHD : ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H) : Subgroup (ModGL τ K) where
  carrier := {g | ∃ h ∈ H, ∃ d ∈ D, g = h * d}
  one_mem' := ⟨1, one_mem H, 1, one_mem D, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨h, hh, d, hd, rfl⟩ ⟨h', hh', d', hd', rfl⟩
    refine ⟨h * (d * h' * d⁻¹), mul_mem hh (hHD d hd h' hh'), d * d', mul_mem hd hd', ?_⟩
    group
  inv_mem' := by
    rintro _ ⟨h, hh, d, hd, rfl⟩
    refine ⟨d⁻¹ * h⁻¹ * d⁻¹⁻¹, hHD d⁻¹ (inv_mem hd) h⁻¹ (inv_mem hh), d⁻¹, inv_mem hd, ?_⟩
    group

theorem fieldAut_mem_semiMulSub {τ : Tag} {H D : Subgroup (ModGL τ K)}
    {hHD : ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H}
    (hσH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H)
    (hσD : ∀ σ : RingAut K, ∀ d ∈ D, fieldAutHom τ K σ d ∈ D) (σ : RingAut K) {g : ModGL τ K}
    (hg : g ∈ semiMulSub H D hHD) : fieldAutHom τ K σ g ∈ semiMulSub H D hHD := by
  obtain ⟨h, hh, d, hd, rfl⟩ := hg
  exact ⟨fieldAutHom τ K σ h, hσH σ h hh, fieldAutHom τ K σ d, hσD σ d hd, map_mul _ _ _⟩

@[expose] def diagFix (σ₀ : RingAut K) : Subgroup (ModGL TwistTag.E6.tag K) where
  carrier := {d | ∃ b : Fin TwistTag.E6.tag.rank → Kˣ,
    (∀ i, b (TwistTag.E6.perm i) = Units.map (σ₀ : K →+* K).toMonoidHom (b i)) ∧
      d = rootDiagUnit TwistTag.E6.tag b}
  one_mem' := ⟨1, fun i => by simp, rootDiagUnit_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    exact ⟨b * b', fun i => by simp [hb, hb'], (rootDiagUnit_mul b b').symm⟩
  inv_mem' := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b⁻¹, fun i => by simp [hb], rootDiagUnit_inv b⟩

section Cert

section Diag

variable {σ₀ : RingAut K}

theorem twistHom_of_mem_diagFix {d : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀) :
    twistHom TwistTag.E6 K (σ₀ : K →+* K) d = d := by
  obtain ⟨b, hb, rfl⟩ := hd
  exact twistHom_rootDiagUnit hb

theorem diagFix_conj_mem_twistedFixedGroup {d g : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀)
    (hg : g ∈ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K)) :
    d * g * d⁻¹ ∈ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
  obtain ⟨b, hb, rfl⟩ := hd
  exact conj_rootDiagUnit_mem_twistedFixedGroup hb hg

theorem diagFix_conj_mem_C0 {d g : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀)
    (hg : g ∈ C0 σ₀) : d * g * d⁻¹ ∈ C0 σ₀ := by
  obtain ⟨b, hb, rfl⟩ := hd
  have h := map_conj_rootDiagUnit_graphFixedRootGroup (σ := (σ₀ : K →+* K)) (t := TwistTag.E6)
    (K := K) hb
  have hmem : rootDiagUnit TwistTag.E6.tag b * g * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈
      (graphFixedRootGroup TwistTag.E6 K (σ₀ : K →+* K)).map
        (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom := ⟨g, hg, rfl⟩
  rw [h] at hmem
  exact hmem

theorem diagFix_conj_mem_inf_parabolicSubgroup {A : Set (Fin TwistTag.E6.tag.rank)}
    {d g : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀)
    (hg : g ∈ parabolicSubgroup TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K)) :
    d * g * d⁻¹ ∈ parabolicSubgroup TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
  refine Subgroup.mem_inf.2 ⟨?_, diagFix_conj_mem_twistedFixedGroup hd (Subgroup.mem_inf.1 hg).2⟩
  obtain ⟨b, -, rfl⟩ := hd
  exact conj_rootDiagUnit_mem_parabolicSubgroupT b (Subgroup.mem_inf.1 hg).1

theorem diagFix_conj_mem_inf_parabolicLevi {A : Set (Fin TwistTag.E6.tag.rank)}
    {d g : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀)
    (hg : g ∈ parabolicLevi TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K)) :
    d * g * d⁻¹ ∈ parabolicLevi TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
  refine Subgroup.mem_inf.2 ⟨?_, diagFix_conj_mem_twistedFixedGroup hd (Subgroup.mem_inf.1 hg).2⟩
  obtain ⟨b, -, rfl⟩ := hd
  exact conj_rootDiagUnit_mem_parabolicLeviT b (Subgroup.mem_inf.1 hg).1

theorem diagFix_conj_mem_inf_parabolicRadical {A : Set (Fin TwistTag.E6.tag.rank)}
    {d g : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀)
    (hg : g ∈ parabolicRadical TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K)) :
    d * g * d⁻¹ ∈ parabolicRadical TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
  refine Subgroup.mem_inf.2 ⟨?_, diagFix_conj_mem_twistedFixedGroup hd (Subgroup.mem_inf.1 hg).2⟩
  obtain ⟨b, -, rfl⟩ := hd
  exact conj_rootDiagUnit_mem_parabolicRadicalT b (Subgroup.mem_inf.1 hg).1

theorem fieldAut_mem_diagFix (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ) (δ : RingAut K)
    {d : ModGL TwistTag.E6.tag K} (hd : d ∈ diagFix σ₀) :
    fieldAutHom TwistTag.E6.tag K δ d ∈ diagFix σ₀ := by
  obtain ⟨b, hb, rfl⟩ := hd
  refine ⟨fun i => Units.map (δ : K →+* K).toMonoidHom (b i), fun i => ?_,
    fieldAutHom_rootDiagUnitT δ b⟩
  dsimp only
  rw [hb i]
  refine Units.ext ?_
  exact congrArg (fun τ : RingAut K => τ ((b i : Kˣ) : K)) (hσ₀c δ)

theorem comm_of_finite [Finite K] (σ₀ δ : RingAut K) : δ * σ₀ = σ₀ * δ :=
  CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K δ σ₀

end Diag

theorem left_mem_normalizer_diag {τ : Tag} {Cg Qg Dg : Subgroup (ModGL τ K)}
    (hCσ : ∀ σ : RingAut K, ∀ h ∈ Cg, fieldAutHom τ K σ h ∈ Cg)
    (hQσ : ∀ σ : RingAut K, ∀ h ∈ Qg, fieldAutHom τ K σ h ∈ Qg)
    (hCD : ∀ d ∈ Dg, ∀ h ∈ Cg, d * h * d⁻¹ ∈ Cg)
    (hQD : ∀ d ∈ Dg, ∀ h ∈ Qg, d * h * d⁻¹ ∈ Qg)
    {α : MulAut ↥Cg} (hα : (Qg.subgroupOf Cg).map α.toMonoidHom = Qg.subgroupOf Cg)
    {s : GamL τ K} {g d : ModGL τ K} (hg : g ∈ Cg) (hd : d ∈ Dg) (hs : s.left = g * d)
    (hspec : ∀ h : ↥Cg, ((α h : ↥Cg) : ModGL τ K) = conjAct τ K s (h : ModGL τ K)) :
    (⟨g, hg⟩ : ↥Cg) ∈ Subgroup.normalizer ((Qg.subgroupOf Cg : Subgroup ↥Cg) : Set ↥Cg) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hdx : d⁻¹ * (x : ModGL τ K) * d ∈ Cg := by
    have := hCD d⁻¹ (inv_mem hd) x x.2
    rwa [inv_inv] at this
  let x'' : ↥Cg := ⟨fieldAutHom τ K s.right⁻¹ (d⁻¹ * (x : ModGL τ K) * d), hCσ _ _ hdx⟩
  have hαx : ((α x'' : ↥Cg) : ModGL τ K) = g * (x : ModGL τ K) * g⁻¹ := by
    rw [hspec, conjAct_apply, hs]
    change g * d * fieldAutHom τ K s.right
      (fieldAutHom τ K s.right⁻¹ (d⁻¹ * (x : ModGL τ K) * d)) * (g * d)⁻¹ = _
    rw [fieldAut_mul_inv_apply]
    group
  have e : (⟨g, hg⟩ * x * (⟨g, hg⟩ : ↥Cg)⁻¹ : ↥Cg) = α x'' :=
    Subtype.ext (by rw [hαx]; rfl)
  have h1 : (α x'' ∈ Qg.subgroupOf Cg) ↔ x'' ∈ Qg.subgroupOf Cg := by
    constructor
    · intro h
      rw [← hα] at h
      obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 h
      have : q = x'' := α.injective hqe
      exact this ▸ hq
    · intro h
      rw [← hα]
      exact Subgroup.mem_map_of_mem _ h
  have h2 : x'' ∈ Qg.subgroupOf Cg ↔ x ∈ Qg.subgroupOf Cg := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h3 := hQσ s.right _ h
      rw [fieldAut_mul_inv_apply] at h3
      have h4 := hQD d hd _ h3
      have e4 : d * (d⁻¹ * (x : ModGL τ K) * d) * d⁻¹ = x := by group
      rwa [e4] at h4
    · intro h
      have h3 := hQD d⁻¹ (inv_mem hd) _ h
      rw [inv_inv] at h3
      exact hQσ _ _ h3
  rw [e]
  exact h2.symm.trans h1.symm

theorem exists_fixed_mem_oppRadical_twistedT [Finite K] [CharP K 2] (σ₀ : RingAut K)
    (hσ₀ : ∀ c, σ₀ (σ₀ c) = c) {J : Set (Fin TwistTag.E6.foldedTag.rank)}
    {S : Subgroup (GamL TwistTag.E6.tag K)}
    (hSL : ∀ s ∈ S, LeviT (TwistTag.E6.orbitUnion J) s)
    (hSΓ : ∀ s ∈ S, twistHom TwistTag.E6 K (σ₀ : K →+* K) s.left = s.left ∧
      s.right * σ₀ = σ₀ * s.right)
    (hodd : Odd (Nat.card S)) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ parabolicRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J)) (hu1 : u ≠ 1)
    (hfix : ∀ s ∈ S, conjAct TwistTag.E6.tag K s u = u) :
    ∃ w ∈ oppRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J), w ≠ 1 ∧
      twistHom TwistTag.E6 K (σ₀ : K →+* K) w = w ∧
      ∀ s ∈ S, conjAct TwistTag.E6.tag K s w = w := by
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical_semiT hτ hSL hodd hu hu1 hfix
  set X : Subgroup (ModGL TwistTag.E6.tag K) :=
    oppRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) ⊓ fixSub S with hX
  have hvX : v ∈ X := Subgroup.mem_inf.2 ⟨hvQ, hvfix⟩
  have hX2 : IsPGroup 2 X :=
    (isPGroup_negUnipotent TwistTag.E6.tag).to_le
      (inf_le_left.trans (oppRadical_le_negUnipotent _))
  have hXne : X ≠ ⊥ := fun h => hv1 (Subgroup.mem_bot.1 (h ▸ hvX))
  have hσ₀' : (σ₀ : K →+* K) ^ TwistTag.E6.order = 1 := by
    show (σ₀ : K →+* K) ^ 2 = 1
    rw [pow_two]
    refine RingHom.ext fun c => ?_
    exact hσ₀ c
  have hFQ := map_twistHom_oppRadical TwistTag.E6 (σ₀ : K →+* K) σ₀.surjective J
  obtain ⟨w, hwX, hw1, hwF⟩ := exists_fixed_ne_one (X := X) hX2 hXne
    (twistHom TwistTag.E6 K (σ₀ : K →+* K))
    (fun x hx => Subgroup.mem_inf.2 ⟨by
        rw [← hFQ]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1,
      fun s hs => by
        rw [← twistHom_conjAct TwistTag.E6 σ₀ s (hSΓ s hs).1 (hSΓ s hs).2,
          (Subgroup.mem_inf.1 hx).2 s hs]⟩)
    (fun x _ => twistHom_iterate_order_of_pow_eq_one (σ₀ : K →+* K) hσ₀' x)
  exact ⟨w, (Subgroup.mem_inf.1 hwX).1, hw1, hwF, (Subgroup.mem_inf.1 hwX).2⟩

variable (σ₀ : RingAut K) in
@[expose] noncomputable def C0D : Subgroup (ModGL TwistTag.E6.tag K) :=
  semiMulSub (C0 σ₀) (diagFix σ₀) fun _ hd _ hh => diagFix_conj_mem_C0 hd hh

variable (σ₀ : RingAut K) in
@[expose] noncomputable def gamTw [Finite K] : Subgroup (GamL TwistTag.E6.tag K) :=
  gamSub (C0D σ₀) fun δ _ hh => fieldAut_mem_semiMulSub
    (fun δ' _ hh' => fieldAut_mem_C0 (comm_of_finite σ₀) δ' hh')
    (fun δ' _ hd' => fieldAut_mem_diagFix (comm_of_finite σ₀) δ' hd') δ hh

theorem mem_gamTw [Finite K] {σ₀ : RingAut K} {s : GamL TwistTag.E6.tag K} :
    s ∈ gamTw σ₀ ↔ ∃ g ∈ C0 σ₀, ∃ d ∈ diagFix σ₀, s.left = g * d :=
  Iff.rfl

variable (σ₀ : RingAut K) in
@[expose] def LiftUniqueTw [Finite K] : Prop :=
  ∀ {s s' : GamL TwistTag.E6.tag K}, s ∈ gamTw σ₀ → s' ∈ gamTw σ₀ →
    (∀ x ∈ C0 σ₀, conjAct TwistTag.E6.tag K s x = conjAct TwistTag.E6.tag K s' x) → s = s'

theorem coe_mulAut_conj {τ : Tag} {H : Subgroup (ModGL τ K)} (g x : ↥H) :
    ((MulAut.conj g x : ↥H) : ModGL τ K) = (g : ModGL τ K) * (x : ModGL τ K) * (g : ModGL τ K)⁻¹ :=
  rfl

theorem conj_assoc_auxTw {M : Type*} [Group M] (g D X : M) :
    g * (D * X * D⁻¹) * g⁻¹ = g * D * X * (g * D)⁻¹ := by
  group

theorem coe_normalActor [Finite K] (σ : K ≃+* K)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (δ : K ≃+* K) (h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ((normalActor σ u δ h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
        ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ := by
  rw [normalActor, MulAut.mul_apply, coe_compatDiagAutHom, coe_fieldActor]

theorem exists_rootDiagUnit_eq_compatDiag_of_conj_mem {t : TwistTag} {σ : K →+* K}
    (hσ : Function.Surjective σ) {h : graphFixedRootGroup t K σ}
    (hA : MulAut.conj h ∈ graphFixedUnipotentStabilizer t K σ) :
    ∃ u, (h : ModGL t.tag K) = rootDiagUnit t.tag (compatDiag t σ u) := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) hV
  have hB : (h : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨h.2, hNU⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  have hC : (graphFixedRootGroup t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
        graphFixedRootGroup t K σ :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  have e : graphFixedRootGroup t K σ ⊓
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) =
        (graphFixedRootBorel t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, hC, Subgroup.map_equiv_normalizer_eq,
      map_conj_graphFixedPosUnipotent hw₀]
  have hB' : (h : ModGL t.tag K) ∈ (graphFixedRootBorel t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← e]
    exact Subgroup.mem_inf.2 ⟨h.2, hNV⟩
  have hH : (h : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
    rw [← graphFixedRootBorel_inf_map_conj hw₀]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  have hT : (h : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).1
  have hΓ : (h : ModGL t.tag K) ∈ twistedFixedGroup t K σ :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).2
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hF := ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hΓ).2
  rw [hb, twistHom_rootDiagUnit_eq] at hF
  have hb' : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i) := by
    intro i
    have h1 := congrFun (rootDiagUnit_injective hF) (t.perm i)
    rw [Equiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := exists_compatDiag_eq hb'
  exact ⟨u, by rw [hu, ← hb]⟩

theorem eq_one_of_conjAct_eq_self [Finite K] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {s : GamL TwistTag.E6.tag K} (hs : s ∈ gamTw σ)
    (hfix : ∀ x ∈ C0 σ, conjAct TwistTag.E6.tag K s x = x) : s = 1 := by
  obtain ⟨g, hg, d, ⟨b, hb, rfl⟩, hsl⟩ := mem_gamTw.1 hs
  have hg' : g ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := hg
  obtain ⟨u, rfl⟩ := exists_compatDiag_eq (σ := σ.toRingHom) hb
  have h0 := (twisted_E6_all_characteristic_common_full_field_parameters Nat.prime_two hf K hK
    σ hσ).1
  have hG : MulAut.conj (⟨g, hg'⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) *
      normalActor σ u s.right = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have h1 := hfix h h.2
    rw [conjAct_apply, hsl] at h1
    rw [MulAut.mul_apply, coe_mulAut_conj, coe_normalActor, MulAut.one_apply]
    exact (conj_assoc_auxTw _ _ _).trans h1
  have hδ : s.right = 1 :=
    delta_eq_of_normalForm_eq_E6
      (g := (⟨g, hg'⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) (g' := 1) (u := u)
      (v := 1) (ε := (1 : RingAut K)) h0
      (by rw [hG, map_one, one_mul, normalActor_one_left, fieldActor_one])
  rw [hδ, normalActor_one_right] at hG
  have hΔ : MulAut.conj (⟨g, hg'⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))⁻¹ =
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right hG
  have hstab : MulAut.conj (⟨g, hg'⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))⁻¹ ∈
      graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom := by
    have := normalActor_mem σ u 1
    rw [normalActor_one_right] at this
    rw [hΔ]
    exact this
  obtain ⟨w, hw⟩ := exists_rootDiagUnit_eq_compatDiag_of_conj_mem (σ := σ.toRingHom)
    σ.surjective hstab
  have hΔw : compatDiagAutHom TwistTag.E6 K σ.toRingHom w =
      MulAut.conj (⟨g, hg'⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))⁻¹ := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_compatDiagAutHom, coe_mulAut_conj, hw]
  have hwu : w = u := compatDiagAutHom_injective (hΔw.trans hΔ)
  rw [hwu] at hw
  have hgd : g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) = 1 := by
    have h1 : g⁻¹ = rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) := hw
    rw [← h1, mul_inv_cancel]
  exact SemidirectProduct.ext (by rw [hsl, hgd, SemidirectProduct.one_left])
    (by rw [hδ, SemidirectProduct.one_right])

theorem lift_unique_twE6 [Finite K] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : LiftUniqueTw σ := by
  intro s s' hs hs' h
  have ht : s'⁻¹ * s ∈ gamTw σ := mul_mem (inv_mem hs') hs
  have h1 : s'⁻¹ * s = 1 := eq_one_of_conjAct_eq_self hf σ hK hσ ht fun x hx => by
    rw [map_mul, MulAut.mul_apply, h x hx, map_inv, MulAut.inv_apply_self]
  exact (inv_mul_eq_one.1 h1).symm

theorem exists_lift_twE6 [Finite K] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ∃ s : GamL TwistTag.E6.tag K, s ∈ gamTw σ ∧
      ∀ h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        ((α h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
          conjAct TwistTag.E6.tag K s h := by
  obtain ⟨g, u, δ, rfl⟩ := exists_normalForm_E6 Nat.prime_two hf hK σ hσ α
  refine ⟨⟨(g : ModGL TwistTag.E6.tag K) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u), δ⟩,
    mem_gamTw.2 ⟨g, g.2, _, ⟨compatDiag TwistTag.E6 σ.toRingHom u, compatDiag_perm u, rfl⟩, rfl⟩,
    fun h => ?_⟩
  rw [MulAut.mul_apply, coe_mulAut_conj, coe_normalActor, conjAct_apply]
  exact conj_assoc_auxTw _ _ _

section LiftTw

variable [Finite K] {σ₀ : RingAut K} {R : Subgroup (MulAut ↥(C0 σ₀))}
  (hR : ∀ α ∈ R, ∃ s : GamL TwistTag.E6.tag K, s ∈ gamTw σ₀ ∧ ∀ h : ↥(C0 σ₀),
    ((α h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) = conjAct TwistTag.E6.tag K s h)

@[expose] noncomputable def liftTT (α : R) : GamL TwistTag.E6.tag K :=
  (hR α α.2).choose

theorem liftTT_mem (α : R) : liftTT hR α ∈ gamTw σ₀ :=
  (hR α α.2).choose_spec.1

theorem liftTT_spec (α : R) (h : ↥(C0 σ₀)) :
    (((α : MulAut ↥(C0 σ₀)) h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) =
      conjAct TwistTag.E6.tag K (liftTT hR α) h :=
  (hR α α.2).choose_spec.2 h

theorem liftTT_spec' (α : R) {x : ModGL TwistTag.E6.tag K} (hx : x ∈ C0 σ₀) :
    (((α : MulAut ↥(C0 σ₀)) ⟨x, hx⟩ : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) =
      conjAct TwistTag.E6.tag K (liftTT hR α) x :=
  liftTT_spec hR α ⟨x, hx⟩

theorem liftTT_mul (hU : LiftUniqueTw σ₀) (α β : R) :
    liftTT hR (α * β) = liftTT hR α * liftTT hR β :=
  hU (liftTT_mem hR _) (mul_mem (liftTT_mem hR α) (liftTT_mem hR β)) fun x hx => by
    rw [map_mul, MulAut.mul_apply, ← liftTT_spec' hR (α * β) hx, ← liftTT_spec' hR β hx,
      ← liftTT_spec hR α, Subgroup.coe_mul, MulAut.mul_apply]

theorem liftTT_one (hU : LiftUniqueTw σ₀) : liftTT hR 1 = 1 := by
  have h := liftTT_mul hR hU 1 1
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

@[expose] noncomputable def liftHomTT (hU : LiftUniqueTw σ₀) : R →* GamL TwistTag.E6.tag K where
  toFun := liftTT hR
  map_one' := liftTT_one hR hU
  map_mul' := liftTT_mul hR hU

theorem liftHomTT_injective (hU : LiftUniqueTw σ₀) : Function.Injective (liftHomTT hR hU) :=
  fun α β h => by
    refine Subtype.ext (MulEquiv.ext fun x => Subtype.ext ?_)
    rw [liftTT_spec hR α, liftTT_spec hR β]
    exact congrArg (fun s => conjAct TwistTag.E6.tag K s (x : ModGL TwistTag.E6.tag K)) h

end LiftTw

variable (σ₀ : RingAut K) in
@[expose] noncomputable def parGD (A : Set (Fin TwistTag.E6.tag.rank)) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  semiMulSub
    (parabolicSubgroup TwistTag.E6.tag K A ⊓ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K))
    (diagFix σ₀) fun _ hd _ hh => diagFix_conj_mem_inf_parabolicSubgroup hd hh

variable (σ₀ : RingAut K) in
@[expose] noncomputable def leviGD (A : Set (Fin TwistTag.E6.tag.rank)) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  semiMulSub
    (parabolicLevi TwistTag.E6.tag K A ⊓ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K))
    (diagFix σ₀) fun _ hd _ hh => diagFix_conj_mem_inf_parabolicLevi hd hh

theorem mem_parGD {σ₀ : RingAut K} {A : Set (Fin TwistTag.E6.tag.rank)}
    {g : ModGL TwistTag.E6.tag K} :
    g ∈ parGD σ₀ A ↔ ∃ p ∈ parabolicSubgroup TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K), ∃ d ∈ diagFix σ₀, g = p * d :=
  Iff.rfl

theorem mem_leviGD {σ₀ : RingAut K} {A : Set (Fin TwistTag.E6.tag.rank)}
    {g : ModGL TwistTag.E6.tag K} :
    g ∈ leviGD σ₀ A ↔ ∃ m ∈ parabolicLevi TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K), ∃ d ∈ diagFix σ₀, g = m * d :=
  Iff.rfl

theorem exists_conj_into_levi_diagFix [Finite K] [CharP K 2] (σ₀ : RingAut K)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {T : Subgroup (GamL TwistTag.E6.tag K)}
    (hT : ∀ s ∈ T, s.left ∈ parGD σ₀ (TwistTag.E6.orbitUnion J))
    (hodd : ¬ 2 ∣ Nat.card T) :
    ∃ y ∈ graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J, ∀ s ∈ T,
      ((SemidirectProduct.inl y : GamL TwistTag.E6.tag K) * s *
        (SemidirectProduct.inl y)⁻¹).left ∈ leviGD σ₀ (TwistTag.E6.orbitUnion J) := by
  have hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ := comm_of_finite σ₀
  have hfinM : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, -, -, -, -, -, -, hdecP, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ₀ J
  obtain ⟨hQAP, -, -, -, -⟩ := parabolic_root_radical_Levi_factors TwistTag.E6.tag K
    (TwistTag.E6.orbitUnion J)
  set A := TwistTag.E6.orbitUnion J with hA
  have hQ2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J) :=
    (isPGroup_posUnipotent 2 TwistTag.E6.tag).to_le
      (inf_le_left.trans (parabolicRadical_le_posUnipotent A))
  refine exists_conj_into_complement (parGD σ₀ A)
    (graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J) (leviGD σ₀ A) hQ2 ?_ ?_ ?_ ?_ ?_
    ?_ ?_ hT hodd
  · intro x hx
    exact mem_parGD.2 ⟨x, Subgroup.mem_inf.2 ⟨hQAP (Subgroup.mem_inf.1 hx).1,
      (Subgroup.mem_inf.1 hx).2⟩, 1, one_mem _, (mul_one x).symm⟩
  · intro x hx y hy
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_parGD.1 hx
    have h1 : d * y * d⁻¹ ∈ graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J :=
      diagFix_conj_mem_inf_parabolicRadical hd hy
    have e : p * d * y * (p * d)⁻¹ = p * (d * y * d⁻¹) * p⁻¹ := by group
    rw [e]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical A (Subgroup.mem_inf.1 hp).1) _).1
        (Subgroup.mem_inf.1 h1).1,
      mul_mem (mul_mem (Subgroup.mem_inf.1 hp).2 (Subgroup.mem_inf.1 h1).2)
        (inv_mem (Subgroup.mem_inf.1 hp).2)⟩
  · exact fun δ _ hh => fieldAut_mem_semiMulSub
      (fun δ' _ hh' => Subgroup.mem_inf.2 ⟨
        fieldAut_mem_parabolicSubgroup δ' (Subgroup.mem_inf.1 hh').1,
        fieldAut_mem_twistedFixedGroup _ σ₀ δ' (hσ₀c δ') (Subgroup.mem_inf.1 hh').2⟩)
      (fun δ' _ hd' => fieldAut_mem_diagFix hσ₀c δ' hd') δ hh
  · exact fun δ _ hh => fieldAut_mem_semiMulSub
      (fun δ' _ hh' => Subgroup.mem_inf.2 ⟨
        fieldAut_mem_parabolicLevi δ' (Subgroup.mem_inf.1 hh').1,
        fieldAut_mem_twistedFixedGroup _ σ₀ δ' (hσ₀c δ') (Subgroup.mem_inf.1 hh').2⟩)
      (fun δ' _ hd' => fieldAut_mem_diagFix hσ₀c δ' hd') δ hh
  · exact fun δ h hh => Subgroup.mem_inf.2 ⟨
      fieldAut_mem_parabolicRadical δ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) (Subgroup.mem_inf.1 hh).2⟩
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxQ, hxM⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨m, hm, d, ⟨b, hb, rfl⟩, hxmd⟩ := mem_leviGD.1 hxM
    have hx1 : x = 1 := eq_one_of_mem_parabolicRadical_of_preservesT (Subgroup.mem_inf.1 hxQ).1
      fun d' x' hx' => by
        rw [hxmd, Units.val_mul, Module.End.mul_apply, coe_rootDiagUnitT]
        exact parabolicLevi_preserves (Subgroup.mem_inf.1 hm).1 d' (rootDiag_mem_gradedT b hx')
    rw [hx1]
    exact one_mem _
  · intro g hg
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_parGD.1 hg
    obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdecP p hp
    exact ⟨qm.1, hq, qm.2 * d, mem_leviGD.2 ⟨qm.2, hm, d, hd, rfl⟩, by rw [hx, mul_assoc]⟩

theorem autCentralizer_inf_rad0_eq_bot_T [Finite K] [CharP K 2] {σ₀ : RingAut K}
    (hσ₀ : ∀ c, σ₀ (σ₀ c) = c) (hU : LiftUniqueTw σ₀)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(C0 σ₀))} (hR : IsPGroup p R)
    (hlift : ∀ α ∈ R, ∃ s : GamL TwistTag.E6.tag K, s ∈ gamTw σ₀ ∧ ∀ h : ↥(C0 σ₀),
      ((α h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) = conjAct TwistTag.E6.tag K s h)
    (hQR : ∀ α ∈ R, (rad0 σ₀ J).map α.toMonoidHom = rad0 σ₀ J)
    (hNQ : Subgroup.normalizer ((rad0 σ₀ J : Subgroup ↥(C0 σ₀)) : Set ↥(C0 σ₀)) = par0 σ₀ J)
    (hC : autCentralizer R ≤ par0 σ₀ J) :
    autCentralizer R ⊓ rad0 σ₀ J = ⊥ := by
  classical
  have hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ := comm_of_finite σ₀
  have hfinM : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : (w₁ : ModGL TwistTag.E6.tag K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  obtain ⟨hQAP, -⟩ := parabolic_root_radical_Levi_factors TwistTag.E6.tag K
    (TwistTag.E6.orbitUnion J)
  set A := TwistTag.E6.orbitUnion J with hA
  set T : Subgroup (GamL TwistTag.E6.tag K) := (liftHomTT hlift hU).range with hT
  have hTcard : Nat.card T = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective (liftHomTT_injective hlift hU)).toEquiv).symm
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]; exact Nat.two_dvd_ne_zero.2 hRodd
  have hQ₀le : ∀ x ∈ graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J,
      x ∈ parabolicRadical TwistTag.E6.tag K A ∧
        x ∈ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := fun x hx => Subgroup.mem_inf.1 hx
  have hTP : ∀ s ∈ T, s.left ∈ parGD σ₀ A := by
    rintro _ ⟨α, rfl⟩
    obtain ⟨g, hg, d, hd, hgd⟩ := mem_gamTw.1 (liftTT_mem hlift α)
    have hmem := left_mem_normalizer_diag (Cg := C0 σ₀)
      (Qg := graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J) (Dg := diagFix σ₀)
      (fun δ h hh => fieldAut_mem_C0 hσ₀c δ hh)
      (fun δ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicRadical δ (hQ₀le h hh).1,
        fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) (hQ₀le h hh).2⟩)
      (fun d hd h hh => diagFix_conj_mem_C0 hd hh)
      (fun d hd h hh => diagFix_conj_mem_inf_parabolicRadical hd hh)
      (hQR α.1 α.2) hg hd hgd (liftTT_spec hlift α)
    have hmem' := hNQ ▸ hmem
    have hgP := graphFixedParabolic_le J (Subgroup.mem_subgroupOf.1 hmem')
    exact mem_parGD.2 ⟨g, hgP, d, hd, hgd⟩
  obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_levi_diagFix σ₀ J hTP hTodd
  set y : GamL TwistTag.E6.tag K := SemidirectProduct.inl y₀ with hy
  set S : Subgroup (GamL TwistTag.E6.tag K) := T.map (MulAut.conj y).toMonoidHom with hS
  have hSM : ∀ s ∈ S, s.left ∈ leviGD σ₀ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hyM s hs
  have hSL : ∀ s ∈ S, LeviT A s := by
    intro s hs
    obtain ⟨m, hm, d, ⟨b, hb, rfl⟩, hmd⟩ := mem_leviGD.1 (hSM s hs)
    exact ⟨m, (Subgroup.mem_inf.1 hm).1, b, hmd⟩
  have hSΓ : ∀ s ∈ S, twistHom TwistTag.E6 K (σ₀ : K →+* K) s.left = s.left ∧
      s.right * σ₀ = σ₀ * s.right := by
    intro s hs
    obtain ⟨m, hm, d, hd, hmd⟩ := mem_leviGD.1 (hSM s hs)
    refine ⟨?_, hσ₀c s.right⟩
    rw [hmd, map_mul, twistHom_of_mem_diagFix hd,
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (Subgroup.mem_inf.1 hm).2).2]
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
    exact Nat.odd_iff.2 hRodd
  have hconjy : ∀ g : ModGL TwistTag.E6.tag K, conjAct _ K y g = y₀ * g * y₀⁻¹ := fun g => by
    rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL TwistTag.E6.tag K, conjAct _ K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K A :=
    (hQ₀le _ (Subgroup.mem_subgroupOf.1 hwQ)).1
  have hy₀A : y₀ ∈ parabolicRadical TwistTag.E6.tag K A := (hQ₀le _ hy₀).1
  have hy₀P : y₀ ∈ parabolicSubgroup TwistTag.E6.tag K A := hQAP hy₀A
  have hu' : y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹ ∈ parabolicRadical TwistTag.E6.tag K A :=
    (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical A hy₀P) _).1
      hu
  have hu'1 : y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct TwistTag.E6.tag K s (w₁ : ModGL TwistTag.E6.tag K) = w₁ := by
    rintro _ ⟨α, rfl⟩
    change conjAct _ K (liftTT hlift α) _ = _
    rw [← liftTT_spec hlift α, hwC α.1 α.2]
  have hfix : ∀ s ∈ S, conjAct TwistTag.E6.tag K s (y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct _ K y⁻¹ (y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹) = w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  obtain ⟨v, hvQ, hv1, hvF, hvfix⟩ := exists_fixed_mem_oppRadical_twistedT σ₀ hσ₀ (J := J)
    (S := S) hSL hSΓ hSodd hu' hu'1 hfix
  have hvG : v ∈ adjointGroup TwistTag.E6.tag K := rootSpan_le_adjointGroup K _ hvQ
  have hvC : v ∈ C0 σ₀ := graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.E6 K
    (σ₀ : K →+* K) (Subgroup.mem_inf.2 ⟨oppRadical_le_negUnipotent A hvQ,
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hvG, hvF⟩⟩)
  have hy₀C : y₀ ∈ C0 σ₀ := graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K
    (σ₀ : K →+* K) J hy₀
  have hwC' : y₀⁻¹ * v * y₀ ∈ C0 σ₀ := mul_mem (mul_mem (inv_mem hy₀C) hvC) hy₀C
  have hwfix : ∀ s ∈ T, conjAct TwistTag.E6.tag K s (y₀⁻¹ * v * y₀) = y₀⁻¹ * v * y₀ := by
    intro s hs
    have h := hvfix _ (Subgroup.mem_map_of_mem _ hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct TwistTag.E6.tag K s (y₀⁻¹ * v * y₀) =
        y₀⁻¹ * (y₀ * conjAct TwistTag.E6.tag K s (y₀⁻¹ * v * y₀) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * v * y₀ := by rw [h]
  have hwcent : (⟨y₀⁻¹ * v * y₀, hwC'⟩ : ↥(C0 σ₀)) ∈ autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    rw [liftTT_spec hlift ⟨α, hα⟩]
    exact hwfix _ ⟨⟨α, hα⟩, rfl⟩
  have hwP : y₀⁻¹ * v * y₀ ∈ graphFixedParabolic TwistTag.E6 K (σ₀ : K →+* K) J :=
    Subgroup.mem_subgroupOf.1 (hC hwcent)
  have hwPA := (graphFixedParabolic_le J hwP).1
  have hvP : v ∈ parabolicSubgroup TwistTag.E6.tag K A := by
    have e : v = y₀ * (y₀⁻¹ * v * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwPA) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)

theorem oppositeFixed_C0_T [Finite K] [CharP K 2] {σ₀ : RingAut K}
    (hσ₀ : ∀ c, σ₀ (σ₀ c) = c) (hU : LiftUniqueTw σ₀)
    (hlift : ∀ α : MulAut ↥(C0 σ₀), ∃ s : GamL TwistTag.E6.tag K, s ∈ gamTw σ₀ ∧
      ∀ h : ↥(C0 σ₀), ((α h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) =
        conjAct TwistTag.E6.tag K s h) :
    OppositeFixed ↥(C0 σ₀) := by
  classical
  have hfinM : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hσ₀' : σ₀ ^ TwistTag.E6.order = 1 := by
    show σ₀ ^ 2 = 1
    rw [pow_two]
    exact RingEquiv.ext hσ₀
  refine oppositeFixed_of_family (rad0 σ₀) (par0 σ₀) (fun J => ?_) (fun J => ?_)
    (fun Q hQ0 hQ2 => ?_) (fun J p hp hp2 R hR hQR hNQ hC => ?_)
  · have h2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J) :=
      (isPGroup_posUnipotent 2 TwistTag.E6.tag).to_le
        (inf_le_left.trans (parabolicRadical_le_posUnipotent _))
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K (σ₀ : K →+* K) J)).symm
  · obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ₀ J
    have hPN := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := hPN (Subgroup.mem_subgroupOf.1 hx)
    simp only [rad0, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  · have hQ₀ne : Q.map (C0 σ₀).subtype ≠ ⊥ := fun h =>
      hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q (C0 σ₀).subtype_injective).1 h)
    obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_fixed TwistTag.E6 σ₀ hσ₀'
      (Subgroup.map_subtype_le Q) (hQ2.map (C0 σ₀).subtype) hQ₀ne
    refine ⟨⟨g, hg⟩, J, fun x hx => Subgroup.mem_subgroupOf.2
      (hP x x.2 (mem_normalizer_map_subtype hx)), fun q hq =>
      Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)⟩
  · exact autCentralizer_inf_rad0_eq_bot_T hσ₀ hU J hp hp2 hR (fun α _ => hlift α) hQR hNQ hC

theorem oppositeFixed_graphFixedRootGroup_E6 [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    OppositeFixed ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have hK2 : Nat.card K = 2 ^ (f * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card_two_pow hK2
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hcard, FiniteField.pow_card]
  exact oppositeFixed_C0_T hσ2 (lift_unique_twE6 hf σ hK hσ) (exists_lift_twE6 hf σ hK hσ)

theorem oppositeFixed_of_twistedChevalleyModel_E6 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel S .E6 (2 ^ f)) : OppositeFixed S := by
  obtain ⟨K, _, hfin, hcard, σ, hσ, ⟨e⟩⟩ := h
  have hK : Nat.card K = (2 ^ f) ^ 2 := hcard
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hK σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ'
  rw [hσσ'] at hZ
  obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  have e'' : S ≃* graphFixedRootGroup TwistTag.E6 K σ'.toRingHom := by
    rw [hσσ']
    exact e.trans e'
  exact oppositeFixed_of_mulEquiv e'' (oppositeFixed_graphFixedRootGroup_E6 σ' hf hK hσ')

end Cert

end CFSG.LieType.ChevTwo.Semi
